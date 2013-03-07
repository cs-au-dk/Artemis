#ifndef TOUCHEVENTPARAMETERS_H
#define TOUCHEVENTPARAMETERS_H
#include "runtime/input/events/eventparameters.h"

namespace artemis{
class TouchEventParameters : public EventParameters
{
public:
    TouchEventParameters();

    QString jsString() const ;
    EventType type() const;

};
}
#endif // TOUCHEVENTPARAMETERS_H
