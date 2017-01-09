#ifndef DIRECTACCESSSYMBOLICVALUES_H
#define DIRECTACCESSSYMBOLICVALUES_H

#include <QString>
#include <QMap>

#ifdef ARTEMIS

namespace Symbolic
{

/*
 * This class is a smiple key-value lookup for the symbolic values which are accessed "directly" using the Artemis
 * symbolic instrumentation input functions.
 * When a JavaScript program calls artemisInputString, artemisInputInteger or artemisInputBoolean, the corresponding
 * symbolic variable is looked up in DirectAccessSymbolicValues and returned (as a symbolic value).
 * Then the concolic mode can notify this class of the new values of each variable on subsequent iterations.
 */
class DirectAccessSymbolicValues
{
public:
    DirectAccessSymbolicValues();

    // Called from Artemis in concolicstandaloneruntime.cpp
    void setString(QString name, QString value);
    void setInteger(QString name, int value);
    void setBoolean(QString name, bool value);

    void reset();

    // Called from JSGlobalObjectFunctions.cpp
    QString getString(QString name);
    int getInteger(QString name);
    bool getBoolean(QString name);

protected:
    QMap<QString, QString> mStringVars;
    QMap<QString, int> mIntegerVars;
    QMap<QString, bool> mBooleanVars;

    // These functions are used to fill the default values of unknown variables.
    // For now they simply return constants.
    QString generateDefaultString();
    int generateDefaultInteger();
    bool generateDefaultBoolean();
};

// Access a single instance.
extern DirectAccessSymbolicValues* direct_access_symbolic_values;
DirectAccessSymbolicValues* get_direct_access_symbolic_values_store();



} // namespace Symbolic
#endif // ARTEMIS
#endif // DIRECTACCESSSYMBOLICVALUES_H
