#ifndef UNKNOWNEVENTPARAMETERS_H
#define UNKNOWNEVENTPARAMETERS_H
#include "runtime/input/events/eventparameters.h"

namespace artemis{
class UnknownEventParameters : public EventParameters
{
public:
    UnknownEventParameters();

    QString jsString() const ;
    EventType type() const;

};
}

#endif // UNKNOWNEVENTPARAMETERS_H
