/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <QString>
#include <QList>
#include <QMap>
#include <QPair>

#ifndef HANDLERDEPENDENCYTRACKER_H
#define HANDLERDEPENDENCYTRACKER_H

namespace artemis
{

/**
 *  This class is used to build a graph of symbolic field reading dependencies between different handlers.
 *  It records when a form field is read during each handler triggering.
 *
 *  Note that this does not give a full picture of which handlers depend on each other (they may do so concretely,
 *  which this class ignores currently).
 */
class HandlerDependencyTracker : public QObject
{
    Q_OBJECT

public:
    HandlerDependencyTracker(bool enabled);

    void writeGraph(QList<int> indexPermutation);

    void beginHandler(QString variable);

    void newIteration();

public slots:
    void slJavascriptSymbolicFieldRead(QString variable, bool isSymbolic);

private:
    bool mEnabled;

    QString mCurrentEvent;
    QList<QString> mEvents;

    const QString mNoEventLabel;

    typedef QPair<QPair<QString, QString>, bool> EdgeDescriptor;
    QMap<EdgeDescriptor, uint> mEdgeCounts;
};

} // namespace artemis
#endif // HANDLERDEPENDENCYTRACKER_H
