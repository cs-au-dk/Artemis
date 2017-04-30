/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "ajaxrequestlistener.h"
#include <QNetworkAccessManager>
#include <QNetworkRequest>
#include <QDebug>


namespace artemis
{

AjaxRequestListener::AjaxRequestListener(QObject* parent) :
    QNetworkAccessManager(parent)
{
}

QNetworkReply* AjaxRequestListener::createRequest(Operation op, const QNetworkRequest& req, QIODevice* outgoingData)

{
    // TODO: Temporary hacking for the demo error injection.
    qDebug() << "REQUEST:" << req.url();
    QMap<QUrl, QUrl> urlReplacements;

    // Beautified, non-bugged.
    //urlReplacements.insert(QUrl("https://goair.in/scripts/combined_ED7BF75BFB56AA42C3CFA51B9EEFA774.js"), QUrl("https://www.cs.ox.ac.uk/people/ben.spencer/downloads/artform-demo-injections/goair-beautified.js"));
    //urlReplacements.insert(QUrl("https://www.goair.in/scripts/combined_ED7BF75BFB56AA42C3CFA51B9EEFA774.js"), QUrl("https://www.cs.ox.ac.uk/people/ben.spencer/downloads/artform-demo-injections/goair-beautified.js"));

    // Minified, bugged.
    //urlReplacements.insert(QUrl("https://goair.in/scripts/combined_ED7BF75BFB56AA42C3CFA51B9EEFA774.js"), QUrl("https://www.cs.ox.ac.uk/people/ben.spencer/downloads/artform-demo-injections/goair-injected-bugs.js"));
    //urlReplacements.insert(QUrl("https://www.goair.in/scripts/combined_ED7BF75BFB56AA42C3CFA51B9EEFA774.js"), QUrl("https://www.cs.ox.ac.uk/people/ben.spencer/downloads/artform-demo-injections/goair-injected-bugs.js"));

    // Beautified, bugged.
    urlReplacements.insert(QUrl("https://goair.in/scripts/combined_ED7BF75BFB56AA42C3CFA51B9EEFA774.js"), QUrl("https://www.cs.ox.ac.uk/people/ben.spencer/downloads/artform-demo-injections/goair-injected-bugs-beautified.js"));
    urlReplacements.insert(QUrl("https://www.goair.in/scripts/combined_ED7BF75BFB56AA42C3CFA51B9EEFA774.js"), QUrl("https://www.cs.ox.ac.uk/people/ben.spencer/downloads/artform-demo-injections/goair-injected-bugs-beautified.js"));

    if (urlReplacements.contains(req.url())) {
        QUrl replacement = urlReplacements[req.url()];
        qDebug() << "REPLACED WITH:" << replacement;

        QNetworkRequest replacementRequest = QNetworkRequest(req);
        replacementRequest.setUrl(replacement);


        //super call
        QNetworkReply* reply2 = QNetworkAccessManager::createRequest(op, replacementRequest, outgoingData);

        if (op == GetOperation)
            { emit this->pageGet(replacement); }
        else if (op == PostOperation)
            { emit this->pagePost(replacement); }

        return reply2;
    }


    //super call
    QNetworkReply* reply = QNetworkAccessManager::createRequest(op, req, outgoingData);

    if (op == GetOperation)
        { emit this->pageGet(req.url()); }
    else if (op == PostOperation)
        { emit this->pagePost(req.url()); }

    return reply;
}

}
