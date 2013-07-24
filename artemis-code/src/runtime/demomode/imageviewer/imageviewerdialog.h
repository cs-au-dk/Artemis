/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#include <QtGui>

#include "imageviewerwidget.h"

#ifndef IMAGEVIEWERDIALOG_H
#define IMAGEVIEWERDIALOG_H

namespace artemis
{


/**
 *  A dialog box which displays images.
 *  In our case it is used to display the generated graphs of trace trees.
 *  Uses ImageViewerWidget for the actual image display.
 */
class ImageViewerDialog : public QDialog
{
public:
    ImageViewerDialog(QString filename, QWidget* parent = 0);

private:
    ImageViewerWidget* mImageView;
};


} // namespace artemis

#endif // IMAGEVIEWERDIALOG_H
