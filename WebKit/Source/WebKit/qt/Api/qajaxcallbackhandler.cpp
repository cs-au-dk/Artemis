
#include <config.h>

#include "WebCore/xml/XMLHttpRequest.h"

#include "qajaxcallbackhandler.h"

QAjaxCallbackHandler::QAjaxCallbackHandler(WebCore::XMLHttpRequest* xhr, QObject *parent) :
    QObject(parent) { 

    m_xhr = xhr;
}

void QAjaxCallbackHandler::dispatch() {
    m_xhr->changeState(WebCore::XMLHttpRequest::DONE);
}

