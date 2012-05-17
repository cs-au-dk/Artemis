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

#include "events/eventypes.h"
#include "variants/randomvariants.h"
#include "events/forms/forminput.h"

#include "randominputgenerator.h"

namespace artemis {

    RandomInputGenerator::RandomInputGenerator(QObject *parent , ArtemisOptions* options, ArtemisTopExecutionListener* execution_listener) :
            AbstractInputGenerator(parent, options, execution_listener)
    {
        Q_CHECK_PTR(options);
        this->var_gen = new RandomVariants(options);
    }

    RandomInputGenerator::~RandomInputGenerator() {
        delete var_gen;
    }

    void RandomInputGenerator::add_new_configurations(const ExecutableConfiguration& configuration, const ExecutionResult& result, WorkList* wl,  ExecutorState* exe_state) {
        Q_CHECK_PTR(wl);
        Q_CHECK_PTR(exe_state);
        
        insert_same_length(configuration, result, *wl, *exe_state);
        insert_extended(configuration, result, *wl, *exe_state);
    }

    void RandomInputGenerator::insert_same_length(const ExecutableConfiguration& e, const ExecutionResult& e_result, WorkList& wl,  ExecutorState& exe_state) {

        EventSequence seq = e.get_eventsequence();
        
        if (seq.empty())
            return;

        EventDescriptor last = seq.last();
        for (int i = 0 ; i++ ; i < this->artemis_options->number_of_samelength()) {
            EventParameters* new_params = 0;
            EventParameters* old_params = last.event_params();

            //Event parameters
            if (old_params->type() == BASE_EVENT) {
                BaseEventParameters bp = var_gen->generate_base_event(last.handler_descriptor().name());
                new_params = new BaseEventParameters(bp);
            }
            else if (old_params->type() == MOUSE_EVENT) {
                MouseEventParameters mp = var_gen->generate_mouse_event(last.handler_descriptor().name());
                new_params = new MouseEventParameters(mp);
            }
            else if (old_params->type() == KEY_EVENT) {
                KeyboardEventParameters kp = var_gen->generate_keyboard_event(last.handler_descriptor().name());
                new_params = new KeyboardEventParameters(kp);
            } else {
                qFatal("Unknown event type!");
                return;
            }

            //Form fields
            FormInput new_form = var_gen->generate_form_fields(last.form_input().fields());

            //Build new Event Descriptor
            EventHandlerDescriptor hh = last.handler_descriptor();
            TargetDescriptor* target = artemis_options->target_generator(hh);

            EventDescriptor new_last(hh, new_form, new_params, target);

            EventSequence new_seq = seq.new_last(new_last);
            ExecutableConfiguration new_conf = e.copy_with_sequence(new_seq);

            wl.add(new_conf, artemis_options->prioritizer().prioritize(new_conf, e_result, exe_state));
            
            delete new_params;
        }
    }

    void RandomInputGenerator::insert_extended(const ExecutableConfiguration& e, const ExecutionResult& e_result, WorkList& wl,  ExecutorState& exe_state) {

        foreach (EventHandlerDescriptor ee, e_result.event_handlers()) {
            EventParameters* new_params = 0;
            EventType tt = get_type(ee.name());
            
            // elfinder specific filtering START

            // filter a number of events
            // if (ee.name() == "mouseover" || 
            //     ee.name() == "mousemove" || 
            //     ee.name() == "mouseout" ||
            //     ee.name() == "dblclick" ||
            //     tt == KEY_EVENT) {

            //     qDebug() << "ELFINDER::FILTERED EVENT #1" << endl;
            //     continue;
            // }

            // if (ee.name() == "mousedown" && ee.dom_element().get_id() != "elfinder") {
            //     qDebug() << "ELFINDER::FILTERED EVENT #2" << endl;
            //     continue;
            // }

            // if (ee.name() == "click" && ee.dom_element().get_tag_name() == "<document>") {
            //     qDebug() << "ELFINDER::FILTERED EVENT #3" << endl;
            //     continue;
            // }

            // if (ee.dom_element().get_id() == "place-root-elfinder-elfinder") {
            //     qDebug() << "ELFINDER::FILTERED EVENT #4" << endl;
            //     continue;
            // }

            // QString class_line = ee.dom_element().get_class();
            
            // if (class_line == "ui-dialog ui-widget ui-widget-content ui-corner-all ui-draggable std42-dialog  elfinder-dialog elfinder-dialog-notify" ||
            //     class_line == "elfinder-path" ||
            //     class_line == "elfinder-quicklook-preview ui-helper-clearfix" ||
            //     class_line == "elfinder-tree elfinder-places ui-corner-all ui-droppable" ||
            //     class_line == "elfinder-tree" ||
            //     class_line == "ui-helper-reset ui-widget elfinder-quicklook ui-draggable ui-resizable" ||
            //     class_line == "ui-helper-reset ui-widget ui-state-default ui-corner-all elfinder-contextmenu elfinder-contextmenu-ltr" ||
            //     class_line == "ui-state-default elfinder-navbar ui-resizable" ||
            //     class_line == "ui-widget-content elfinder-button elfinder-button-search" ||
            //     class_line == "ui-helper-reset ui-helper-clearfix ui-widget ui-widget-content ui-corner-all elfinder elfinder-ltr ui-resizable elfinder-disabled" ||
            //     class_line == "ui-widget-content elfinder-toolbar-button-separator" ||
            //     class_line == "ui-icon ui-icon-close") {
            //     qDebug() << "ELFINDER::FILTERED EVENT #5" << endl;
            //     continue;
            // }

            // if (class_line.contains("std42-dialog")) {
            //     qDebug() << "ELFINDER::FILTERED EVENT #6" << endl;
            //     continue;
            // }

            // elfinder specific filtering END


            //Event parameters
            if (tt == BASE_EVENT) {
                new_params = new BaseEventParameters(var_gen->generate_base_event(ee.name()));
            } else if (tt == MOUSE_EVENT) {
                new_params = new MouseEventParameters(var_gen->generate_mouse_event(ee.name()));
            } else if (tt == KEY_EVENT) {
                new_params = new KeyboardEventParameters(var_gen->generate_keyboard_event(ee.name()));
            } else if (tt == TOUCH_EVENT) {
                qDebug() << "TODO: Support touch events";
                continue;
            } else if (tt == UNKNOWN_EVENT) {
                qDebug() << "TODO: Support event: " << ee.name();
                continue;
            }

            //Form fields
            QSet<FormField> fd = e_result.form_fields();
            FormInput new_form = var_gen->generate_form_fields(fd);
            artemis_options->target_generator(ee);

            TargetDescriptor* target = artemis_options->target_generator(ee);
            EventDescriptor eh(ee, new_form, new_params, target);

            ExecutableConfiguration new_conf(e.get_eventsequence().extend(eh), e.starting_url());
            wl.add(new_conf, artemis_options->prioritizer().prioritize(new_conf, e_result, exe_state));

            delete new_params;
        }
    }

    void RandomInputGenerator::reprioritize() {

    }

}
