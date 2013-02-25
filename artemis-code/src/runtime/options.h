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

#include "runtime/worklist/worklist.h"
#include "strategies/termination/terminationstrategy.h"
#include "strategies/prioritizer/prioritizerstrategy.h"
#include "strategies/inputgenerator/targets/targetdescriptor.h"
#include "runtime/events/eventhandlerdescriptor.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"

namespace artemis
{

enum FormInputGenerationStrategies {
    Random, ConstantString
};

enum CoverageReport {
    STDOUT, HTML, NONE
};

typedef struct OptionsType {

    OptionsType() :
        iterationLimit(1),
        numberSameLength(1),
        recreatePage(false),
        formInputGenerationStrategy(Random),
        outputCoverage(NONE)
    {}

    QMap<QString, QString> presetFormfields;
    QMap<QString, QString> presetCookies;

    int iterationLimit;
    int numberSameLength;

    bool recreatePage;

    QString useProxy;
    QString dumpPageStates;

    FormInputGenerationStrategies formInputGenerationStrategy;

    CoverageReport outputCoverage;

} Options;

}
#endif // ARTEMISOPTIONS_H
