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

#include "handlerdependencytracker.h"

#include "util/fileutil.h"

#include <assert.h>
#include <QDebug>
#include <QRegExp>

namespace artemis
{

HandlerDependencyTracker::HandlerDependencyTracker(bool enabled) :
    mEnabled(enabled)
{
    mCurrentEvent = mNoEventLabel;
}

void HandlerDependencyTracker::writeGraph()
{
    if(!mEnabled) {
        return;
    }

    QString filename = "handlers.gv";

    QString graph = "digraph {\n  node [shape = \"rectangle\", style = \"filled\", fillcolor = \"forestgreen\"];\n\n";

    QMap<QString, QString> names;

    // Declare each node.
    int idx = 1;
    foreach(QString label, mEvents) {
        names.insert(label, QString("event_%1").arg(idx));
        graph += QString("  %1 [label = \"%2\"];\n").arg(names[label], label);
        idx++;
    }
    // Check for any which were not listed in the event sequence...
    QSet<QString> extras;
    foreach(EdgeDescriptor edge, mEdgeCounts.keys()) {
        assert(mEvents.contains(edge.first.first) || edge.first.first == mNoEventLabel);
        if(!mEvents.contains(edge.first.second)) {
            names.insert(edge.first.second, QString("unknown_%1").arg(idx));
            graph += QString("  %1 [label = \"%2\", fillcolor = \"lightpink\"];\n").arg(names[edge.first.second], edge.first.second);
            idx++;
            extras.insert(edge.first.second);
        }
    }
    // Sanity check for any variable reads not coming from a known handler.
    QSet<QString> observed;
    foreach(EdgeDescriptor edge, mEdgeCounts.keys()) {
        observed.insert(edge.first.first);
    }
    if(observed.contains(mNoEventLabel)) {
        names.insert(mNoEventLabel, QString("no_source"));
        graph += QString("  no_source [label = \"%1\", fillcolor = \"lightpink\"];\n").arg(mNoEventLabel);
        mEvents.prepend(mNoEventLabel);
    }
    observed.subtract(extras);
    assert(mEvents.toSet().contains(observed));

    graph += "\n";

    // Add invisible edges which keep the main sequence in line.
    for(int i = 0; i < mEvents.length() - 1; i++) {
        graph += QString("  %1 -> %2 [style = \"invis\", weight = \"100\"];\n").arg(names[mEvents.at(i)], names[mEvents.at(i+1)]);
    }

    graph += "\n";

    // Add the edges.
    foreach(EdgeDescriptor edge, mEdgeCounts.keys()) {
        graph += QString("  %1 -> %2 [label = \" %3\" color = \"%4\"];\n").arg(names[edge.first.first],
                                                                            names[edge.first.second],
                                                                            QString::number(mEdgeCounts[edge]),
                                                                            (edge.second ? "blue" : "red"));
    }

    // Finish
    graph += "\n}\n";

    writeStringToFile(filename, graph);
}

void HandlerDependencyTracker::beginHandler(QString variable)
{
    if(!mEnabled) {
        return;
    }

    mCurrentEvent = variable;
    if(!mEvents.contains(variable)) {
        mEvents.append(variable);
    } else {
        qDebug() << "Warning: Duplicate event name" << variable << "seen in HandlerDependencyTracker.";
    }
}

void HandlerDependencyTracker::newIteration()
{
    // Reset mEvents, so we only keep the version from the latest run.
    // In fact it should be the same on every iteration (except the initial load...).
    mEvents.clear();
    mCurrentEvent = mNoEventLabel;
}

void HandlerDependencyTracker::slJavascriptSymbolicFieldRead(QString variable, bool isSymbolic)
{
    if(!mEnabled) {
        return;
    }

    variable.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    EdgeDescriptor edge;
    edge.first.first = mCurrentEvent;
    edge.first.second = variable;
    edge.second = isSymbolic;

    mEdgeCounts[edge] += 1;
}


} // namespace artemis
