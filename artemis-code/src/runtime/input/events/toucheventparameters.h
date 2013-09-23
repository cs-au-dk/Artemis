#ifndef TOUCHEVENTPARAMETERS_H
#define TOUCHEVENTPARAMETERS_H
#include "runtime/input/events/eventparameters.h"

namespace artemis{
class TouchEventParameters : public EventParameters
{
public:
    TouchEventParameters();

    QString getJsString() const ;
    EventType getType() const;

};
}
#endif // TOUCHEVENTPARAMETERS_H
