#ifndef JAVASCRIPTSTATISTICS_H
#define JAVASCRIPTSTATISTICS_H

#include <QObject>
#include <QSharedPointer>
#include <QSet>
#include <QHash>

#include "runtime/input/baseinput.h"

namespace artemis {

class JavascriptStatistics : public QObject
{

    Q_OBJECT

public:
    JavascriptStatistics();

    void notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent);

    QSet<QString> getPropertiesWritten(const QSharedPointer<const BaseInput>& input) const;
    QSet<QString> getPropertiesRead(const QSharedPointer<const BaseInput>& input) const;

private:

    // InputHash -> set<PropertyString>
    QHash<uint, QSet<QString>* > mPropertyReadSet;

    // InputHash -> set<PropertyString>
    QHash<uint, QSet<QString>* > mPropertyWriteSet;

    uint mInputBeingExecuted;

public slots:
    void slJavascriptPropertyRead(QString propertyName);
    void slJavascriptPropertyWritten(QString propertyName);

};

typedef QSharedPointer<JavascriptStatistics> JavascriptStatisticsPtr;

}

#endif // JAVASCRIPTSTATISTICS_H
