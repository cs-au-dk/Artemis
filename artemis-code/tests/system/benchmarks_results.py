#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/legacy-benchmarks/'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

import time
from harness.environment import WebServer
from harness.artemis import execute_artemis


def run_lambda(f, tries=3):
    try:
        start_t = time.time()
        result = f()
        end_t = time.time()
    except Exception:
        return run_lambda(f, tries - 1) if tries <= 1 else {"result": -1, "time": -1, "attempts": 4 - tries}

    return {"result": result, "time": end_t - start_t, "attempts": 4 - tries}


def generate_reports(name, path, exclude):
    url = WEBSERVER_URL + "/" + path
    print ("Testing: %s" % url)
    events_r = run_lambda(lambda: execute_artemis(name, url,
                                                  iterations=100,
                                                  strategy_form_input='random',
                                                  strategy_priority='constant',
                                                  exclude=exclude))
    const_r = run_lambda(lambda: execute_artemis(name, url,
                                                 iterations=100,
                                                 strategy_form_input='javascript-constants',
                                                 strategy_priority='constant',
                                                 exclude=exclude))
    cov_r = run_lambda(lambda: execute_artemis(name, url,
                                               iterations=100,
                                               strategy_form_input='javascript-constants',
                                               strategy_priority='coverage',
                                               exclude=exclude))
    all_r = run_lambda(lambda: execute_artemis(name, url,
                                               iterations=100,
                                               strategy_form_input='javascript-constants',
                                               strategy_priority='all',
                                               exclude=exclude))
    return {
        "events": events_r,
        "const": const_r,
        "cov": cov_r,
        "all": all_r}


def log_result_to_file(file_name, result):
    with open(file_name, 'a') as fp:
        fp.write("%s\n" % ",".join(map(lambda i: str(i), result)))
    return file_name


def set_up_file():
    file_name = 'benchmark_results-%s.csv' % int(time.time())
    with open(file_name, 'w') as fp:
        fp.write(
            "Benchmark,Cov: events,Time: events,Tries:events,Cov: const,Time: const,Tries:const,Cov: cov,Time: cov," +
            "Tries:cov,Cov: all,Time: all,Tries:all\n")
    return file_name


def run_old_benchmarks(benchmarks):
    file_name = set_up_file()
    for benchmark in benchmarks:
        exclude = map(lambda e: WEBSERVER_URL + "/" + e, benchmark['exclude']) if "exclude" in benchmark else []
        name = benchmark['name']
        path = benchmark['path']
        reports = generate_reports(name, path, exclude)
        results = [name,
                   reports['events']['result']['WebKit::coverage::covered-unique'],
                   reports['events']['time'],
                   reports['events']['attempts'],
                   reports['const']['result']['WebKit::coverage::covered-unique'],
                   reports['const']['time'],
                   reports['const']['attempts'],
                   reports['cov']['result']['WebKit::coverage::covered-unique'],
                   reports['cov']['time'],
                   reports['cov']['attempts'],
                   reports['all']['result']['WebKit::coverage::covered-unique'],
                   reports['all']['time'],
                  reports['cov']['attempts']]
        log_result_to_file(file_name, results)


if __name__ == '__main__':
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    benchmarks = [
        {"name": "3dmodel", "path": "3dmodel/index.html"},
        {"name": "ajax-poller", "path": "ajax-poller/ajax-poller.php"},
        {"name": "ball-pool", "path": "ball_pool/index.html", "exclude": ["ball_pool/js/box2d.js",
                                                                          "ball_pool/js/protoclass.js"]},
        {"name": "dragable-boxes", "path": "dragable-boxes/dragable-boxes.html"},
        {"name": "dynamic-articles", "path": "dynamicArticles/index.html"},
        {"name": "fractal-viewer", "path": "fractal_viewer/index.html",
         "exclude": ['fractal_viewer/js/lib/jquery-1.3.js']},
        {"name": "homeostasis", "path": "homeostasis/index.html"},
        {"name": "pacman", "path": "pacman/index.html",
         "exclude": ["pacman/src/js/pacman10-hp.2.js",
                     "pacman/src/js/pacman10-hp.js"]},
        {"name": "htmledit", "path": "htmledit/demo_full.html",
         "exclude": ["htmledit/htmlbox.min.js",
                     "htmledit/htmlbox.undoredomanager.js",
                     "htmledit/jquery-1.3.2.min.js"]},
        {"name": "ajaxtabs", "path": "ajaxtabs/demo.htm"}
    ]
    run_old_benchmarks(benchmarks)
    del server
