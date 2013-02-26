
#include <iostream>

#include "statistics/statsstorage.h"

#include "javascriptstatistics.h"

namespace artemis {

JavascriptStatistics::JavascriptStatistics() :
    QObject(NULL),
    mInputBeingExecuted(0)
{
}

void JavascriptStatistics::notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent)
{
    mInputBeingExecuted = inputEvent->hashCode();

    if (!mPropertyReadSet.contains(mInputBeingExecuted)) {
        mPropertyReadSet.insert(mInputBeingExecuted, new QSet<QString>());
    }

    if (!mPropertyWriteSet.contains(mInputBeingExecuted)) {
        mPropertyWriteSet.insert(mInputBeingExecuted, new QSet<QString>());
    }
}

void JavascriptStatistics::slJavascriptPropertyRead(QString propertyName)
{
    statistics()->accumulate("WebKit::readproperties", 1);

    if (mInputBeingExecuted != 0) {
        mPropertyReadSet.value(mInputBeingExecuted)->insert(propertyName);
    }
}

void JavascriptStatistics::slJavascriptPropertyWritten(QString propertyName)
{
    statistics()->accumulate("WebKit::writtenproperties", 1);

    if (mInputBeingExecuted != 0) {
        mPropertyWriteSet.value(mInputBeingExecuted)->insert(propertyName);
    }
}

QSet<QString> JavascriptStatistics::getPropertiesWritten(const QSharedPointer<const BaseInput>& input) const
{
    uint hashcode = input->hashCode();

    if (mPropertyWriteSet.contains(hashcode)) {
        return *mPropertyWriteSet.value(hashcode);
    }

    return QSet<QString>();
}

QSet<QString> JavascriptStatistics::getPropertiesRead(const QSharedPointer<const BaseInput>& input) const
{
    uint hashcode = input->hashCode();

    if (mPropertyReadSet.contains(hashcode)) {
        return *mPropertyReadSet.value(hashcode);
    }

    return QSet<QString>();
}

}
