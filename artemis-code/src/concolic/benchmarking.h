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

#ifndef BENCHMARKING_H
#define BENCHMARKING_H

#include <QFlags>

namespace artemis
{

enum ConcolicBenchmarkFeatureValues {
    ALL_ENABLED = 0,
    RADIO_RESTRICTION = 1,
    SELECT_RESTRICTION = 2,
    SELECT_RESTRICTION_DYNAMIC = 4,
    SELECT_LINK_VALUE_INDEX = 8,
    CVC4_COERCION_OPT = 16,
    CONCRETE_VALUE_PROPERTY = 32,
    EVENT_SEQUENCE_SYNC_INJECTIONS = 64
};

Q_DECLARE_FLAGS(ConcolicBenchmarkFeatures, ConcolicBenchmarkFeatureValues)
Q_DECLARE_OPERATORS_FOR_FLAGS(ConcolicBenchmarkFeatures)



} // namespace artemis
#endif // BENCHMARKING_H
