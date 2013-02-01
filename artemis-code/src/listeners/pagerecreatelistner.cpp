#include "pagerecreatelistner.h"

#include "util/fileutil.h"
#include "util/urlutil.h"
#include "runtime/ajax/ajaxrequest.h"

namespace artemis {

PageRecreateListner::PageRecreateListner()
{
}

void PageRecreateListner::artemis_start(const QUrl& url) {
    QString dirname = url.encodedHost();
    dirname = dirname.isEmpty() ? "ARTEMIS_RIP" : dirname;
    Q_ASSERT(base_dir.mkpath("./" + dirname));
    this->base_dir = QDir("./" + dirname);
    this->base_url = url;
    qDebug() << "PAGE RECREATE MODE: Artemis will attempt to store " << url.toString() <<
                " in a workable state in " << base_dir.absolutePath();
}

void PageRecreateListner::loaded_page(const ArtemisWebPage& page) {
    QUrl base_url = page.mainFrame()->url();
    //Save the page
    QString page_contents = read_entire_page(base_url);
    write_string_to_file(base_dir.absoluteFilePath("index.html"), page_contents);

    //Save statically linked scripts.
    QWebFrame* mf = page.mainFrame();
    QWebElementCollection scts = mf->findAllElements("script");
    foreach (QWebElement script_tag, scts) {
        if (!script_tag.hasAttribute("src"))
            continue;
        QString src_tag = script_tag.attribute("src");
        QUrl url = QUrl(src_tag);
        if (script_urls_fetched.contains(get_hash(url,1)))
            continue;
        script_urls_fetched << get_hash(url,1);
        if (!url.isRelative()) {
            qDebug() << "RECREATE-WARN: Cannot save absolute URL " << src_tag;
            continue;
        }

        QString script_text = read_entire_page(base_url.resolved(QUrl(src_tag)));
        QString s_path = base_dir.absolutePath() + "/" + get_path_part_of_url(src_tag);
        base_dir.mkpath(s_path);
        QString final_path = s_path + "/" + get_filename_part_of_url(src_tag);
        write_string_to_file(final_path, script_text);
        qDebug() << "RECREATE: Script " << src_tag << " was saved to " << final_path;
    }
}

void PageRecreateListner::executed(const ExecutableConfiguration& conf, const ExecutionResult* result) {
    foreach (AjaxRequest r, result->ajax_request()) {
        QUrl url = r.url();
        if (ajax_urls_fetched.contains(url))
            continue;
        if (!url.isRelative()) {
            url = to_relative(base_url,url);
        }
        ajax_urls_fetched << url;
        if (!url.isRelative()) {
            qDebug() << "RECREATE-WARN: Cannot save AJAX request to absolute URL " << url.toString();
            continue;
        }
        bool is_post = r.post_data().isEmpty();

        //Rerun the request
        QString res = is_post ? read_entire_page(r.url(),r.post_data()) : read_entire_page(r.url());

        //Create matching dir structure
        QString a_path = get_path_part_of_url(url.toString());
        base_dir.mkpath(base_dir.absolutePath() + "/" + a_path);
        QString final_path = base_dir.absolutePath() + "/" + a_path + "/" + get_filename_part_of_url(url.toString());
        qDebug() << "RECREATE: Writing ajax request for url: " << r.url() << " to " << final_path;
        write_string_to_file(final_path, res);
    }
}

void PageRecreateListner::code_loaded(QString source, QUrl url, int startline) {
    if (script_urls_fetched.contains(get_hash(url,startline)))
        return;
    if (url == base_url)
        return;
    if (is_omit(url))
        return;
    QUrl rel_url = url;//to_relative(base_url,url);

    QString a_path = get_path_part_of_url(rel_url.toString());
    base_dir.mkpath(base_dir.absolutePath() + "/" + a_path);
    QString final_path = base_dir.absolutePath() + "/" + a_path + "/" + get_filename_part_of_url(rel_url.toString());
    qDebug() << "RECREATE: Writing code load for url: " << rel_url << " to " << final_path;
    write_string_to_file(final_path, source);
}

}
