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


#ifndef IMAGEVIEWERWIDGET_H
#define IMAGEVIEWERWIDGET_H

namespace artemis
{


/**
 *  A widget for displaying images.
 *  The images can be scrolled and zoomed from the widget.
 */
class ImageViewerWidget : public QScrollArea
{
public:
    ImageViewerWidget(QString filename, QWidget* parent = 0);

private:
    QLabel* mImage;
    QPixmap mPixmap;
};


} // namespace artemis

#endif // IMAGEVIEWERWIDGET_H
