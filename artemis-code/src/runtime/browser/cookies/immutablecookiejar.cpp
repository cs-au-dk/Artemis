/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <QList>
#include <QNetworkCookie>
#include <QDebug>
#include "immutablecookiejar.h"

namespace artemis
{

ImmutableCookieJar::ImmutableCookieJar(const QMap<QString, QString> &initialstate, const QString& domain)
    : QNetworkCookieJar()
{
    foreach(QString key, initialstate.keys()) {
        QNetworkCookie* cookie = new QNetworkCookie(key.toAscii(), initialstate[key].toAscii());
        cookie->setPath(QString("/"));
        cookie->setDomain(domain);
        mCookies.append(*cookie);
    }
    this->setAllCookies(mCookies);
}

QList<QNetworkCookie> ImmutableCookieJar::cookiesForUrl(const QUrl& url) const
{
    return mCookies;
}

bool ImmutableCookieJar::setCookiesFromUrl(const QList<QNetworkCookie> &cookieList, const QUrl& url)
{
    return true;
}

}
