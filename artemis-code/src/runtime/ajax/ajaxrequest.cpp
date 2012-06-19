#include "ajaxrequest.h"

namespace artemis {

AjaxRequest::AjaxRequest(const QUrl url, const QString post_data)
{
    this->m_post_data = post_data;
    this->m_url = url;
}

QUrl AjaxRequest::url() const {
    return m_url;
}

QString AjaxRequest::post_data() {
    return m_post_data;
}

bool AjaxRequest::operator==(const AjaxRequest &other) const {
    return m_url == other.url() && m_post_data == other.m_post_data;
}

QDebug operator<<(QDebug dbg, const AjaxRequest &e) {
    dbg.nospace() << "AjaxRequest[url = " << e.m_url << ",post_data = " << e.m_post_data << "]";
    return dbg.space();
}

uint AjaxRequest::hashcode() const {
    return qHash(m_url)*17 + qHash(m_post_data)*23;
}


}
