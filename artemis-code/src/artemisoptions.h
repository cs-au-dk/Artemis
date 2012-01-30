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
#ifndef ARTEMISOPTIONS_H
#define ARTEMISOPTIONS_H

#include <QObject>
#include <QUrl>
#include <QSettings>
#include <worklist/worklist.h>
#include "termination/terminationstrategy.h"
#include "priortizer/abstractprioritizer.h"
#include "listeners/artemistopexecutionlistener.h"
#include "listeners/multiplexlistener.h"

namespace artemis {

    class AbstractInputGenerator;
    class AbstractPrioritizer;

    class ArtemisOptions : public QObject
    {
        Q_OBJECT
    public:
        explicit ArtemisOptions(QObject *parent = 0);
        void setURL(QUrl* url);
        QUrl* getURL();
        int random_seed();
        int next_random();
        /**
          How many sequence of same length should be added?
          */
        int number_of_samelength();
        AbstractInputGenerator* create_input_generator();
        WorkList* work_list();
        TerminationStrategy* termination();
        ExecutableConfiguration& initial_configuration();
        AbstractPrioritizer& prioritizer();
        bool is_preset_field(QString id);
        QString get_present_value(QString id);
        void add_preset_field(QString id, QString value);
        void print_presets();
        void add_artemis_execution_listner(ArtemisTopExecutionListener* l);
        void dump_page_states(QString target_dir);
        ArtemisTopExecutionListener* get_listner();
        /**
          parse strings on the form id=value and add to the set of preset formfields.
          */
        void parse_and_add_option_string(QString s);
        QMap<QString,QString> get_preset_fields();
        bool dump_urls();
        void set_dump_urls(bool v);
        void set_recreate_page(bool v);
        bool recreate_page();

        void set_proxy(QString s);
        void set_preset_cookie(QString s);
        QMap<QString, QString> get_preset_cookies();
        void set_number_of_iterations(QString iterations);

    private:
        QUrl* artemis_url;
        ExecutableConfiguration* initial_conf;
        AbstractPrioritizer* pri;
        QMap<QString, QString> preset_formfields;
        bool m_dump_urls;
        MultiplexListener* m_multi;
        bool m_recreate_page;
        QString m_proxy_address;
        QMap<QString, QString> m_preset_cookies;
        int m_number_of_iterations;


    signals:


    public slots:

    };

}
#endif // ARTEMISOPTIONS_H
