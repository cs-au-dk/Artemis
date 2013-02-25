#ifndef LOGGINGUTIL_H
#define LOGGINGUTIL_H
#include <string>
#include <iostream>
#include <Qt>
#include <QChar>
#include <QStringRef>
#include <QTextStream>
#include <QSet>
#include <algorithm>
#include <set>
#endif // LOGGINGUTIL_H
using namespace std;
namespace artemis{
enum LogLevel {ERROR, WARNING, INFO, DEBUG,FATAL,ALL,OFF};

class Log{
private:
    static set<artemis::LogLevel> levels;
    static string logLevelToString(LogLevel level){
        string result;
        switch(level){
        case ERROR:
            result = "ERROR";
            break;
        case FATAL:
            result = "FATAL";
        break;
        case WARNING:
            result = "WARNING";
            break;
        case INFO:
            result = "INFO";
            break;
        case DEBUG:
            result = "DEBUG";
            break;
        case OFF:
            result= "OFF";
            break;
        case ALL:
            result = "ALL";
            break;
        }
        return result;
    }


public:
    static void log(string message,LogLevel level){
        if(Log::hasLogLevel(level)){
            cout << message << endl;
        }
    }

    static void error(string message){
        Log::log(message,ERROR);
    }
    static void fatal(string message){
        Log::log(message,FATAL);
    }

    static void warning(string message){
        Log::log(message,WARNING);
    }
    static void debug(string message){
        Log::log(message,DEBUG);
    }
    static void info(string message){
        Log::log(message,INFO);
    }
    static void addLogLevel(LogLevel level){
        if(level != OFF){
            Log::levels.insert(level);
        } else {
            Log::levels.clear();
        }
    }

    static bool hasLogLevel(LogLevel level){
        return level == INFO || levels.find(level) != levels.end() ||
                levels.find(artemis::ALL) != levels.end();
    }
};



}
