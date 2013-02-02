#include "ajaxrequest.h"

namespace artemis
{

AjaxRequest::AjaxRequest(const QUrl url, const QString postData)
{
    this->mPostData = postData;
    this->mUrl = url;
}

QUrl AjaxRequest::url() const
{
    return mUrl;
}

QString AjaxRequest::postData()
{
    return mPostData;
}

QDebug operator<<(QDebug dbg, const AjaxRequest& e)
{
    dbg.nospace() << "AjaxRequest[url = " << e.mUrl << ",postData = " << e.mPostData << "]";
    return dbg.space();
}

}
