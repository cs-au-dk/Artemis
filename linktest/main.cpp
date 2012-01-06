#include <QtWebKit>
#include <QApplication>
#include "qwebexecutionlistener.h"


int main(int argc, char *argv[])
{
    QCoreApplication a(argc, argv);
    inst::ExecutionListener *b = new inst::ExecutionListener();
    //QWebExecutionListener n();
   // installWebKitExecutionListener(new inst::ExecutionListener());
    return a.exec();
}
