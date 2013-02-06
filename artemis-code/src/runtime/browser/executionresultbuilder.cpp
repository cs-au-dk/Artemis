#include "executionresultbuilder.h"

#include "statistics/statsstorage.h"

namespace artemis
{

ExecutionResultBuilder::ExecutionResultBuilder(QObject* parent, QWebPage* page) : QObject(parent)
{
    mPage = page;
    reset();
}

void ExecutionResultBuilder::reset()
{
    mResult = QSharedPointer<ExecutionResult>(new ExecutionResult());
    mElementPointers.clear();
    mPageStateAfterLoad = QString("");
}

void ExecutionResultBuilder::notifyPageLoaded()
{
    mPageStateAfterLoad = mPage->mainFrame()->toHtml();
}

QSharedPointer<ExecutionResult> ExecutionResultBuilder::getResult()
{
    registerFromFieldsIntoResult();
    registerEventHandlersIntoResult();

    mResult->mPageContents = mPage->mainFrame()->toHtml();
    mResult->mStateHash = qHash(mResult->mPageContents);
    mResult->mModifiedDom = mResult->mPageContents.localeAwareCompare(mPageStateAfterLoad) != 0;

    return mResult;
}

void ExecutionResultBuilder::registerEventHandlersIntoResult()
{

    QPair<QWebElement*, QString> p;
    foreach(p, mElementPointers) {
        if (getType(p.second) == UNKNOWN_EVENT) {
            qWarning() << "WARN: Ignoring unsupported event of type " << p.second;
            continue;
        }

        if (p.first->isNull()) {
            qWarning() << "WARN: Got event handler with NULL element. Assuming document is reciever";
        }

        qDebug() << "Finalizing " << p.second << "  " << p.first->tagName() << " _T: "
                 << p.first->attribute(QString("title"));

        EventHandlerDescriptor* handler = new EventHandlerDescriptor(this, p.first, p.second);

        if (handler->isInvalid()) {
            qWarning() << "WARN: element was invalid, ignoring";
        } else {
            mResult->mEventHandlers.insert(handler);
        }
    }

}

void ExecutionResultBuilder::registerFromFieldsIntoResult()
{
    QSet<QWebFrame*> ff = getAllFrames();

    foreach(QWebFrame * f, ff) {
        QWebElementCollection inputs = f->findAllElements("input");
        foreach(QWebElement i, inputs) {
            FormFieldTypes fType =  getTypeFromAttr(i.attribute("type"));

            if (fType == NO_INPUT)
                { continue; }

            QSharedPointer<FormField> formf = QSharedPointer<FormField>(new FormField(fType, new DOMElementDescriptor(0, &i)));
            mResult->mFormFields.insert(formf);
        }

        //Gather <textarea> elements
        QWebElementCollection textareas = f->findAllElements("textarea");
        foreach(QWebElement ta, textareas) {
            QSharedPointer<FormField> taf = QSharedPointer<FormField>(new FormField(TEXT, new DOMElementDescriptor(0, &ta)));
            mResult->mFormFields.insert(taf);
        }

        //Gather select tags
        QWebElementCollection selects = f->findAllElements("select");
        foreach(QWebElement ss, selects) {
            QSet<QString> options = getSelectOptions(ss);
            QSharedPointer<FormField> ssf = QSharedPointer<FormField>(new FormField(FIXED_INPUT, new DOMElementDescriptor(0, &ss), options));
            mResult->mFormFields.insert(ssf);
        }
    }
}

QSet<QWebFrame*> ExecutionResultBuilder::getAllFrames()
{
    QSet<QWebFrame*> res;
    QWebFrame* main = mPage->mainFrame();
    res.insert(main);
    QList<QWebFrame*> worklist;
    worklist.append(main);

    while (!worklist.isEmpty()) {
        QWebFrame* c = worklist.takeFirst();
        worklist += c->childFrames();
        res += c->childFrames().toSet();
    }

    return res;
}

QSet<QString> ExecutionResultBuilder::getSelectOptions(const QWebElement& e)
{
    QSet<QString> res;
    QWebElementCollection options = e.findAll("option");
    foreach(QWebElement o, options) {
        QString valueAttr = o.attribute("value");

        if (!valueAttr.isEmpty())
            { valueAttr = o.toPlainText(); }

        if (valueAttr.isEmpty()) {
            qWarning() << "WARN: Found empty option element in select, ignoring";
            continue;
        }

        res << valueAttr;
    }
    return res;
}

/** LISTENERS **/

void ExecutionResultBuilder::slEventListenerAdded(QWebElement* elem, QString name)
{
    Q_CHECK_PTR(elem);

    qDebug() << "Artemis detected new eventhandler for event: " << name << " tag name: "
             << elem->tagName() << " id: " << elem->attribute(QString("id")) << " title "
             << elem->attribute(QString("title")) << "class: " << elem->attribute("class") << endl;

    if (isNonInteractive(name)) {
        return;
    }

    mElementPointers.insert(QPair<QWebElement*, QString>(elem, name));
}

void ExecutionResultBuilder::slEventListenerRemoved(QWebElement* elem, QString name)
{
    qDebug() << "Artemis removed eventhandler for event: " << name << " tag name: "
             << elem->tagName() << " id: " << elem->attribute(QString("id")) << " title "
             << elem->attribute(QString("title")) << "class: " << elem->attribute("class") << endl;

    if (isNonInteractive(name)) {
        return;
    }

    mElementPointers.remove(QPair<QWebElement*, QString>(elem, name));
}

void ExecutionResultBuilder::slTimerAdded(int timerId, int timeout, bool singleShot)
{
    qDebug() << "Artemis::Timer " << timerId << " added";
    statistics()->accumulate("timers::registered", 1);
    mResult->mTimers.insert(timerId, QSharedPointer<Timer>(new Timer(timerId, timeout, singleShot)));
}

void ExecutionResultBuilder::slTimerRemoved(int timerId)
{
    qDebug() << "Artemis::Timer " << timerId << " removed";
    mResult->mTimers.remove(timerId);
}

void ExecutionResultBuilder::slStringEvaled(const QString exp)
{
    qDebug() << "WEBKIT: Evaled string: " << exp;
    mResult->mEvaledStrings << exp;
}

void ExecutionResultBuilder::slCodeLoaded(intptr_t _, QString src, QUrl url, int li)
{
    qDebug() << "WebKitExecutor::slCodeLoaded" << endl;
}

void ExecutionResultBuilder::slScriptCrashed(QString cause, intptr_t sourceID, int lineNumber)
{
    qDebug() << "WEBKIT SCRIPT ERROR: " << cause << " line: " << lineNumber << " source: "
             << sourceID << endl;
}

void ExecutionResultBuilder::slAjaxCallbackHandlerAdded(int callbackId)
{
    qDebug() << "AJAX CALLBACK HANDLER ADDED" << endl;
    mResult->mAjaxCallbackHandlers.append(callbackId);
}

void ExecutionResultBuilder::slAjaxRequestInitiated(QUrl u, QString postData)
{
    QSharedPointer<AjaxRequest> req = QSharedPointer<AjaxRequest>(new AjaxRequest(u, postData));
    qDebug() << "Adding AJAX request: " << req;
    mResult->mAjaxRequest.insert(req);
}

}
