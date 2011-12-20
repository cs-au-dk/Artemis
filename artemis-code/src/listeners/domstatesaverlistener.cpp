#include <QTextStream>

#include <QFileInfo>
#include "domstatesaverlistener.h"
#include "util/fileutil.h"
#include "util/urlutil.h"
#include "artemisglobals.h"

namespace artemis {

DOMStateSaverListener::DOMStateSaverListener(QString path)
{
    this->save_to_path = path;
    this->iter = 0;
    this->did_dump_url_state = false;
}

DOMStateSaverListener::~DOMStateSaverListener() {
   // delete net_access;
}

void DOMStateSaverListener::executed(const ExecutableConfiguration& _, ExecutorState* exe_state, const ExecutionResult& result) {
    if (!result.modifed_dom()) {
        return;
    }
    QString filename = save_to_path + "/state_dump_" + QString::number(iter++) + ".html";
    this->created_html_files << filename;
    qDebug() << "Saving DOM state to: " << filename;
    QString dom_data = exe_state->get_page_from_hash(result.page_state_hash());
    write_string_to_file(filename, dom_data);
}

void DOMStateSaverListener::loaded_page(const ArtemisWebPage& page, ExecutorState* exe_state) {
    if (did_dump_url_state)
        return;
    this->state_after_onload = page.mainFrame()->toHtml();
    this->initial_url_state = read_entire_page(page.mainFrame()->url());
    did_dump_url_state = true;
}



void DOMStateSaverListener::artemis_finished(ExecutorState* exe_state) {
    //Save pre onload state
    QString filename = save_to_path + "/state_dump_preonload" + ".html";
    qDebug() << "Saving DOM preonload state to: " << filename;
    write_string_to_file(filename, this->initial_url_state);

    //Save post onload state
    QString filename2 = save_to_path + "/state_dump_postonload" + ".html";
    qDebug() << "Saving DOM post onload state to: " << filename2;
    write_string_to_file(filename2, this->state_after_onload);

    //Write html file linking to all states
    create_index();
}

void DOMStateSaverListener::create_index() {
    QString idx_filename = save_to_path + "/index.html";
    qDebug() << "Writing DOM state index file to " << idx_filename;
    QFile idx(idx_filename);
    idx.open(QFile::WriteOnly | QFile::Truncate);
    QTextStream out(&idx);
    out << INDEX_HEADER;
    out << "\n";
    foreach (QString p , created_html_files) {
        QString n = QFileInfo(p).fileName();
        out << "<li><a href=\""<< n << "\">" << n << "</a></li>\n";
    }
    out << INDEX_FOOTER;
    out.flush();
    idx.close();
}


}
