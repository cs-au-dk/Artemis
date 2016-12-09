#include "directaccesssymbolicvalues.h"

#ifdef ARTEMIS


namespace Symbolic
{

DirectAccessSymbolicValues::DirectAccessSymbolicValues()
{
}

void DirectAccessSymbolicValues::setString(QString name, QString value)
{
    mStringVars.insert(name, value);
}

void DirectAccessSymbolicValues::setInteger(QString name, int value)
{
    mIntegerVars.insert(name, value);
}

void DirectAccessSymbolicValues::setBoolean(QString name, bool value)
{
    mBooleanVars.insert(name, value);
}

void DirectAccessSymbolicValues::reset()
{
    mStringVars.clear();
    mIntegerVars.clear();
    mBooleanVars.clear();
}

QString DirectAccessSymbolicValues::getString(QString name)
{
    // If this name is not known, generate a default value and save it.
    if (!mStringVars.contains(name)) {
        setString(name, generateDefaultString());
    }
    return mStringVars[name];
}

int DirectAccessSymbolicValues::getInteger(QString name)
{
    // If this name is not known, generate a default value and save it.
    if (!mIntegerVars.contains(name)) {
        setInteger(name, generateDefaultInteger());
    }
    return mIntegerVars[name];
}

bool DirectAccessSymbolicValues::getBoolean(QString name)
{
    // If this name is not known, generate a default value and save it.
    if (!mBooleanVars.contains(name)) {
        setInteger(name, generateDefaultBoolean());
    }
    return mBooleanVars[name];
}

QString DirectAccessSymbolicValues::generateDefaultString()
{
    return QString();
}

int DirectAccessSymbolicValues::generateDefaultInteger()
{
    return 0;
}

bool DirectAccessSymbolicValues::generateDefaultBoolean()
{
    return false;
}


DirectAccessSymbolicValues* direct_access_symbolic_values = 0;
DirectAccessSymbolicValues* get_direct_access_symbolic_values_store()
{
    if (direct_access_symbolic_values == 0) {
        direct_access_symbolic_values = new DirectAccessSymbolicValues();
    }
    return direct_access_symbolic_values;
}




} // namespace Symbolic
# endif

