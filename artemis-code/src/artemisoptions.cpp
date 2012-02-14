/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.
  
  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:
  
     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.
  
     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.
  
  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  
  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
*/
#include "artemisoptions.h"
#include <cstdlib>
#include "inputgenerator/abstractinputgenerator.h"
#include "inputgenerator/randominputgenerator.h"
#include "worklist/deterministicworklist.h"
#include "termination/numberofiterationstermination.h"
#include "events/eventhandlerdescriptor.h"
#include  <QUrl>
#include <QNetworkProxy>
#include "priortizer/constantprioritizer.h"
#include "listeners/domstatesaverlistener.h"
#include "listeners/pagerecreatelistner.h"
#include "inputgenerator/targets/targetdescriptor.h"
#include "inputgenerator/targets/legacytarget.h"
#include "inputgenerator/targets/jquerytarget.h"

namespace artemis {

    ArtemisOptions::ArtemisOptions(QObject *parent) :
            QObject(parent)
    {
        artemis_url = new QUrl();
        initial_conf = NULL;
        m_multi = new MultiplexListener(0);
        m_jquery_listener = new JQueryListener();
        this->pri = 0;
        m_number_of_iterations = 4;
    }

    void ArtemisOptions::setURL(QUrl* url) {
        artemis_url = url;
    }

    QUrl* ArtemisOptions::getURL() {
        return artemis_url;
    }

    int ArtemisOptions::random_seed() {
        return 0;
    }

    int ArtemisOptions::next_random() {
        return rand();
    }

    int ArtemisOptions::number_of_samelength() {
        return 1;
    }

    AbstractInputGenerator* ArtemisOptions::create_input_generator() {
        return new RandomInputGenerator(NULL,this, this->m_multi);
    }

    WorkList* ArtemisOptions::work_list() {
        return new DeterministicWorkList();
    }

    TerminationStrategy* ArtemisOptions::termination() {
        return new NumberOfIterationsTermination(m_number_of_iterations);
    }

    ExecutableConfiguration& ArtemisOptions::initial_configuration() {
        if (initial_conf == 0)
            initial_conf =  new ExecutableConfiguration(EventSequence(), QUrl(""));
        return *initial_conf;
    }

    AbstractPrioritizer& ArtemisOptions::prioritizer() {
        if (pri == 0)
            pri = new ConstantPrioritizer(this);
        return *pri;
    }

    bool ArtemisOptions::is_preset_field(QString id) {
        return preset_formfields.contains(id);
    }

    QString ArtemisOptions::get_present_value(QString id) {
        if (is_preset_field(id))
            return preset_formfields[id];
        else
            return "";
    }

    void ArtemisOptions::add_preset_field(QString id, QString value) {
        preset_formfields.insert(id,value);
    }

    QMap<QString,QString> ArtemisOptions::get_preset_fields() {
        return preset_formfields;
    }

    bool ArtemisOptions::dump_urls() {
        return this->m_dump_urls;
    }

    void ArtemisOptions::set_dump_urls(bool v) {
        this->m_dump_urls = v;
    }

    void ArtemisOptions::parse_and_add_option_string(QString s) {
        QStringList ls = s.split("=");
        Q_ASSERT(ls.size() == 2);
        qDebug() << ls;
        this->add_preset_field(ls.at(0), ls.at(1));
    }

    void ArtemisOptions::print_presets() {
        qDebug() << "Preset form fields (id -> value map)";
        foreach (QString id, this->preset_formfields.keys()) {
            qDebug() << "  " << id << " : " << preset_formfields[id] ;
        }
        qDebug() << "";

        qDebug() << "Preset cookies (id -> value map)";
        foreach (QString id, m_preset_cookies.keys()) {
            qDebug() << "  " << id << " : " << m_preset_cookies[id];
        }
        qDebug() << "";
    }

    void ArtemisOptions::add_artemis_execution_listner(ArtemisTopExecutionListener* l) {
        Q_CHECK_PTR(m_multi);
        Q_CHECK_PTR(l);
        this->m_multi->add_listener(l);
    }

    ArtemisTopExecutionListener* ArtemisOptions::get_listner() {
        return this->m_multi;
    }

    JQueryListener* ArtemisOptions::get_jquery_listener() {
        return this->m_jquery_listener;
    }

    TargetDescriptor* ArtemisOptions::target_generator(EventHandlerDescriptor event_handler) {
        TargetDescriptor* target = new JQueryTarget(event_handler, this);
        //TargetDescriptor* target = new LegacyTarget(event_handler);
        return target;
    }

    void ArtemisOptions::dump_page_states(QString target_dir) {
        this->add_artemis_execution_listner(new DOMStateSaverListener(target_dir));
    }

    void ArtemisOptions::set_recreate_page(bool v) {
        this->m_recreate_page = v;
        if (v) {
            this->add_artemis_execution_listner(new PageRecreateListner());
        }
    }

    bool ArtemisOptions::recreate_page() {
        return this->m_recreate_page;
    }

    void ArtemisOptions::set_proxy(QString s) {
        m_proxy_address = s;
        QStringList parts = s.split(QString(":"));

        QNetworkProxy proxy(QNetworkProxy::HttpProxy, parts.at(0), parts.at(1).toShort());
        QNetworkProxy::setApplicationProxy(proxy);
    }

    void ArtemisOptions::set_preset_cookie(QString s) {
        QStringList parts = s.split(QString("="));
        m_preset_cookies.insert(parts.at(0), parts.at(1));
    }

    QMap<QString, QString> ArtemisOptions::get_preset_cookies() {
        return m_preset_cookies;
    }

    void ArtemisOptions::set_number_of_iterations(QString iterations) {
        m_number_of_iterations = iterations.toInt();
    }

}
