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
#include <assert.h>
#include <typeinfo>

#include "runtime/events/eventypes.h"
#include "variants/randomvariants.h"
#include "runtime/events/forms/forminput.h"
#include "runtime/input/baseinput.h"
#include "runtime/input/dominput.h"
#include "runtime/input/timerinput.h"
#include "runtime/input/ajaxinput.h"

#include "randominputgenerator.h"

namespace artemis
{

RandomInputGenerator::RandomInputGenerator(QObject *parent,
		TargetGenerator* targetGenerator,
		int numberSameLength) :
    InputGeneratorStrategy(parent)
{
	mTargetGenerator = targetGenerator;
	mTargetGenerator->setParent(this);

	mNumberSameLength = numberSameLength;

    var_gen = new RandomVariants();
}

RandomInputGenerator::~RandomInputGenerator()
{
    delete var_gen;
}

QList<ExecutableConfiguration*> RandomInputGenerator::add_new_configurations(const ExecutableConfiguration* configuration,
    const ExecutionResult& result)
{
    QList<ExecutableConfiguration*> newConfigurations;

    newConfigurations.append(insert_same_length(configuration, result));
    newConfigurations.append(insert_extended(configuration, result));

    return newConfigurations;
}

QList<ExecutableConfiguration*> RandomInputGenerator::insert_same_length(const ExecutableConfiguration* e,
    const ExecutionResult& e_result)
{
    QList<ExecutableConfiguration*> newConfigurations;

    InputSequence* seq = e->get_eventsequence();

    if (seq->isEmpty())
        return newConfigurations;

    BaseInput* last = seq->getLast();
    for (int i = 0; i++; i < mNumberSameLength) {
        BaseInput* new_last = this->permutate_input(last);

        if (last->isEqual(new_last) == false) {
            InputSequence* new_seq = seq->copy();
            new_seq->replaceLast(new_last);

            ExecutableConfiguration* new_conf = new ExecutableConfiguration(e->parent(), new_seq, e->starting_url());

            newConfigurations.append(new_conf);
        }
    }

    return newConfigurations;
}

BaseInput *RandomInputGenerator::permutate_input(const DomInput *input)
{
    EventParameters* new_params = var_gen->generate_event_parameters(input->getEventHandler());

    if (new_params == NULL) {
        qFatal("Unknown event type!");
        assert(false);
    }

    //Form fields
    FormInput new_form = var_gen->generate_form_fields(input->getFormInput().fields());

    //Build new Event Descriptor
    EventHandlerDescriptor hh = input->getEventHandler();
    TargetDescriptor* target = mTargetGenerator->generateTarget(hh);

    DomInput *new_last = new DomInput(0, hh, new_form, new_params, target);

    return new_last;
}

// TODO should be const
BaseInput* RandomInputGenerator::permutate_input(BaseInput* input)
{
    return input;
}

QList<ExecutableConfiguration*> RandomInputGenerator::insert_extended(const ExecutableConfiguration* oldConfiguration,
    const ExecutionResult& result)
{
    QList<ExecutableConfiguration*> newConfigurations;

    foreach (EventHandlerDescriptor ee, result.event_handlers()) {
        EventParameters* new_params = var_gen->generate_event_parameters(ee);

        if (new_params == NULL) {
            qFatal("Unknown event type!");
            assert(false);
        }

        //Form fields
        QSet<FormField> fd = result.form_fields();
        FormInput new_form = var_gen->generate_form_fields(fd);

        TargetDescriptor* target = mTargetGenerator->generateTarget(ee);
        DomInput* domInput = new DomInput(0, ee, new_form, new_params, target);

        InputSequence* newInputSequence = oldConfiguration->get_eventsequence()->copy();
        newInputSequence->extend(domInput);

        ExecutableConfiguration* newConfiguration = new ExecutableConfiguration(0, newInputSequence, oldConfiguration->starting_url());

        newConfigurations.append(newConfiguration);
    }

    foreach (const Timer timer, result.get_timers()) {
        TimerInput* new_input = new TimerInput(0, timer);

        InputSequence* new_seq = oldConfiguration->get_eventsequence()->copy();
        new_seq->extend(new_input);

        ExecutableConfiguration* new_conf = new ExecutableConfiguration(0, new_seq, oldConfiguration->starting_url());

        newConfigurations.append(new_conf);
    }

    qDebug() << "INSERTING AJAX HANDLERS" << endl;
    foreach (int callbackId, result.ajaxCallbackHandlers()) {
        qDebug() << "HIT" << endl;
        AjaxInput* newInput = new AjaxInput(0, callbackId);

        InputSequence* newSequence = oldConfiguration->get_eventsequence()->copy();
        newSequence->extend(newInput);

        ExecutableConfiguration* newConfiguration = new ExecutableConfiguration(0, newSequence,
            oldConfiguration->starting_url());

        newConfigurations.append(newConfiguration);
    }

    return newConfigurations;
}

}
