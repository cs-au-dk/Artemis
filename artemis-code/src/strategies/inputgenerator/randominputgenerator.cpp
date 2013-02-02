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

RandomInputGenerator::RandomInputGenerator(QObject* parent,
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

QList<QSharedPointer<ExecutableConfiguration> > RandomInputGenerator::add_new_configurations(const QSharedPointer<ExecutableConfiguration> configuration,
        const ExecutionResult& result)
{
    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    newConfigurations.append(insert_same_length(configuration, result));
    newConfigurations.append(insert_extended(configuration, result));

    return newConfigurations;
}

QList<QSharedPointer<ExecutableConfiguration> > RandomInputGenerator::insert_same_length(const QSharedPointer<ExecutableConfiguration> e,
        const ExecutionResult& e_result)
{
    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    const InputSequence* seq = e->getInputSequence();

    if (seq->isEmpty())
        { return newConfigurations; }

    BaseInput* last = seq->getLast();

    for (int i = 0; i < mNumberSameLength; i++) {
        BaseInput* new_last = this->permutate_input(last);

        if (last->isEqual(new_last) == false) {
            InputSequence* new_seq = seq->copy();
            new_seq->replaceLast(new_last);

            QSharedPointer<ExecutableConfiguration> new_conf = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(new_seq, e->getUrl()));

            newConfigurations.append(new_conf);
        }
    }

    return newConfigurations;
}

BaseInput* RandomInputGenerator::permutate_input(const DomInput* input)
{
    EventParameters* newParams = var_gen->generate_event_parameters(NULL, input->getEventHandler());
    FormInput* newForm = var_gen->generate_form_fields(NULL, input->getFormInput()->getFields());
    TargetDescriptor* target = mTargetGenerator->generateTarget(NULL, input->getEventHandler());
    EventHandlerDescriptor* newEventHandlerDescriptor = new EventHandlerDescriptor(NULL, input->getEventHandler());

    DomInput* newLast = new DomInput(NULL, newEventHandlerDescriptor, newForm, newParams, target);

    return newLast;
}

// TODO should be const
BaseInput* RandomInputGenerator::permutate_input(BaseInput* input)
{
    return input;
}

QList<QSharedPointer<ExecutableConfiguration> > RandomInputGenerator::insert_extended(const QSharedPointer<ExecutableConfiguration> oldConfiguration,
        const ExecutionResult& result)
{
    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    foreach(EventHandlerDescriptor * ee, result.event_handlers()) {

        EventParameters* new_params = var_gen->generate_event_parameters(NULL, ee);
        FormInput* new_form = var_gen->generate_form_fields(NULL, result.form_fields());
        TargetDescriptor* target = mTargetGenerator->generateTarget(NULL, ee);
        DomInput* domInput = new DomInput(NULL, ee, new_form, new_params, target);

        InputSequence* newInputSequence = oldConfiguration->getInputSequence()->copy();
        newInputSequence->extend(domInput);

        QSharedPointer<ExecutableConfiguration> newConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(newInputSequence, oldConfiguration->getUrl()));

        newConfigurations.append(newConfiguration);
    }

    foreach(const QSharedPointer<Timer> timer, result.get_timers()) {
        TimerInput* new_input = new TimerInput(0, timer);

        InputSequence* new_seq = oldConfiguration->getInputSequence()->copy();
        new_seq->extend(new_input);

        QSharedPointer<ExecutableConfiguration> new_conf = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(new_seq, oldConfiguration->getUrl()));

        newConfigurations.append(new_conf);
    }

    qDebug() << "INSERTING AJAX HANDLERS" << endl;
    foreach(int callbackId, result.ajaxCallbackHandlers()) {
        qDebug() << "HIT" << endl;
        AjaxInput* newInput = new AjaxInput(0, callbackId);

        InputSequence* newSequence = oldConfiguration->getInputSequence()->copy();
        newSequence->extend(newInput);

        QSharedPointer<ExecutableConfiguration> newConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(newSequence,
                oldConfiguration->getUrl()));

        newConfigurations.append(newConfiguration);
    }

    return newConfigurations;
}

}
