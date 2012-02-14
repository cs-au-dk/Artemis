
#ifndef QAJAXCALLBACKHANDLER_H
#define QAJAXCALLBACKHANDLER_H

#include <QtCore/qobject.h>
#include "qwebkitglobal.h"

namespace WebCore {
    class XMLHttpRequest;
}

class QWEBKIT_EXPORT QAjaxCallbackHandler : public QObject
{
    Q_OBJECT

public:
    explicit QAjaxCallbackHandler(WebCore::XMLHttpRequest*, QObject *parent = 0);
    void dispatch();

protected:
    WebCore::XMLHttpRequest* m_xhr;
};

#endif // QAJAXCALLBACKHANDLER_H

