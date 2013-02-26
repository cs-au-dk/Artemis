#ifndef JAVASCRIPTSTATISTICS_H
#define JAVASCRIPTSTATISTICS_H

#include <QObject>
#include <QSharedPointer>

namespace artemis {

class JavascriptStatistics : public QObject
{

    Q_OBJECT

public:
    JavascriptStatistics();

public slots:
    void slJavascriptPropertyRead(QString propertyName);
    void slJavascriptPropertyWritten(QString propertyName);

};

typedef QSharedPointer<JavascriptStatistics> JavascriptStatisticsPtr;

}

#endif // JAVASCRIPTSTATISTICS_H
