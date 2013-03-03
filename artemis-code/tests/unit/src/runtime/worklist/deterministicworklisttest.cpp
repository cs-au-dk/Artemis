
#include <QSharedPointer>
#include <QUrl>

#include "include/gtest/gtest.h"

#include "runtime/worklist/worklist.h"
#include "runtime/worklist/deterministicworklist.h"
#include "runtime/executableconfiguration.h"
#include "runtime/input/inputsequence.h"

namespace artemis
{

TEST(DeterministicWorklistTest, Dummy) {

    DeterministicWorkListPtr worklist = new DeterministicWorkList(NULL);

    QUrl url;
    QSharedPointer<InputSequence> inputSequence = QSharedPointer<InputSequence>(new InputSequence());
    QSharedPointer<ExecutableConfiguration> executableConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(inputSequence, url));

    ASSERT_EQ(worklist->size(), 0);
    worklist->add(executableConfiguration, 0);
    ASSERT_EQ(worklist->size(), 1);

}

}
