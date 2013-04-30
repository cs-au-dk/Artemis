
$.fn.updateOLOffset = function () {
    if ($(this).hasClass('startline')) {
        var nr = $(this).attr('class').replace(/.*startlinenr\[([0-9]+)\].*/, '$1');
        $(this).find('ol').attr('start', nr);
        $(this).removeClass('startline');
    }
};

$.fn.updateOffset = function () {
    var self = $(this);
    if (self.size() > 1) {
        self.each(function () {
            $(this).updateOffset();
        });
        return;
    }

    if (!self.hasClass('expanded')) {
        self.css('top', '');
        return;
    }
    var code = self.next('pre');
    var codeOff = code.offset();

    var i = (codeOff.top - (self.outerHeight())) - ($(window).scrollTop());
    self.css('top', Math.max(0, Math.min(i * -1, code.outerHeight())));

};

$.fn.markLineCoverage = function (cover, className) {

    if (cover == undefined) {
        cover = coverage;
    }

    if (className == undefined) {
        className = 'covered';
    }
    var self = $(this);
    var id = self.parents('div').attr('id');
    var i, start = (i = self.find('ol.linenums').first().attr('start')) == undefined ? 1 : i;
    var cov = cover[id];

    $.each(cov, function (k, v) {
        $(self.find('ol.linenums > li').get(v - start)).addClass(className);
    });

};

$.fn.markRangeCoverage = function (cover,className) {
    var self = $(this);
    if(self.size() > 1){
        self.each(function(e){
            e.markRangeCoverage();
        });
        return;
    }
    if (cover == undefined) {
        cover = coverageRange;
    }

    if (className == undefined) {
        className = 'covered';
    }
    var id = self.parents('div').attr('id');
    var cov = cover[id];
    var lineMarker = function (self,l,v){
        var newL = l+ self.text().replace("&gt;",">").replace("&lt;","<").replace("&amp;","&").length;
        var endChar = v[3] >= 0?v[3]:newL+1;
        if((v[1]< l && endChar > l) || (v[1]<newL && endChar>newL)){
            self.addClass(className);
        }

        return newL;
    };
    $.each(cov,function(k,v){
        if(v.length != 4){
            return;
        }

        var stline = $("ol.linenums > li:eq("+(v[0]-1)+")",self),
            endline = v[0] == v[2]? stline:$("ol.linenums > li:eq("+(v[2]-1)+")",self);
        if(stline == endline){
            var l = 0;
            stline.children('span').each(function(){l = lineMarker($(this),l,v)});
        } else {
            var l = 0;
            stline.children('span').each(function(){l = lineMarker($(this),l,[v[0],v[1],v[2],-1])});
            l = 0;
            endline.children('span').each(function(){l = lineMarker($(this),l,[v[0],0,v[2],v[3]])});
        }
    });
};

$.fn.toggleExpandCode = function (callback) {
    if (callback == undefined) {
        callback = function () {
        };
    }
    var self = $(this);
    var pre = self.parent().find('pre');
    if (self.hasClass('expanded')) {
        pre.hide();
        self.removeClass('expanded');
        self.updateOffset();
        $(window).scrollTop(Math.min(self.offset().top, $(window).scrollTop()));
        self.text('show code coverage');
    } else {
        pre.show();
        if (!pre.hasClass('prettyprinted')) {
            pre.addClass('prettyprint');
            prettyPrint(function () {
                pre.removeClass('prettyprint');
                pre.updateOLOffset();
                pre.markLineCoverage();
                pre.markLineCoverage(symbolicCoverage, 'symCovered');
                pre.markRangeCoverage();
                pre.markRangeCoverage(symbolicCoverageRange,'symCovered');
                callback();
            });
        } else {
            callback();
        }
        self.addClass('expanded');
        self.text('hide');
    }

};

$.fn.blinkLine = function () {
    var self = $(this);
    self.css('opacity', 0);
    self.animate({opacity: 1}, 300);
};

$.fn.scrollToLine = function () {
    var line = (this);
    var lineOffTop = line.offset().top;
    var win = $(window), winScrollTop = win.scrollTop() + 200;
    if (winScrollTop > lineOffTop || winScrollTop + win.height() - 400 < lineOffTop + line.outerHeight()) {
        win.scrollTop(lineOffTop - (win.height() - line.outerHeight()) / 2);
    }
};

function setUpSymbolicInfo() {
    var numLines = 0, currentLine = null;
    $.each(symbolicCoverage, function (k, v) {
        numLines += v.length;
    });

    var symbolicNavigator = $('<div id="SymbolicNavigator">' + numLines + ' symbolic tainted lines found.</div>');
    symbolicNavigator.appendTo('body');
    if (numLines > 0) {
        var scrollToFunction = function (i) {
            i = (ii = i % numLines) >= 0 ? ii : numLines + ii;
            currentLine = i;
            var codeDivList = $('div.code');
            var id = null, iii, j, ii = iii = 0;
            while (id == null) {
                id = $(codeDivList[ii]).attr('id');
                j = iii;
                iii += symbolicCoverage[id].length;
                id = iii > i ? $(codeDivList[ii]) : null;
                ii++;
            }
            var expandLink;
            var scrollAndMark = function () {
                var line = id.find('ol.linenums > li.symCovered:eq(' + (i - j) + ')');
                line.scrollToLine();
                line.blinkLine();

            };
            if (!(expandLink = id.find('a.expandLink')).hasClass('expanded')) {
                expandLink.toggleExpandCode(scrollAndMark);
            } else {
                scrollAndMark();
            }

        };

        var nextLink = $('<a href="#">next line</a>'),
            prevLink = $('<a href="#">previous line</a> ')
        symbolicNavigator.append(" Go to ");
        symbolicNavigator.append(prevLink);
        symbolicNavigator.append(" - ");
        symbolicNavigator.append(nextLink);
        prevLink.click(function () {
            scrollToFunction(currentLine == null ? 0 : currentLine - 1);
            return false;
        });
        nextLink.click(function () {
            scrollToFunction(currentLine == null ? 0 : currentLine + 1);
            return false;
        });
    }

}

function linkToCode() {
    var query = window.location.search.substr(1).split('&');
    var code = null;
    var line = null;
    
    for(var i=0; i<query.length; i++){
        var pieces = query[i].split('=');
        if(pieces.length == 2){
            if(pieces[0] == 'code'){
                code = pieces[1];
            }else if(pieces[0] == 'line'){
                line = parseInt(pieces[1], 10);
            }
        }
    }
    
    if(code !== null && line !== null){
        $('#' + code).first().each(function(){
            $('.expandLink', this).first().toggleExpandCode();
            
            $('ol.linenums', this).first().each(function(){
                var start;
                if ($(this).attr('start') === undefined) {
                    start = 1
                } else {
                    start = parseInt($(this).attr('start'), 10)
                }
                $('li', this).eq(line - start).scrollToLine();
                $('li', this).eq(line - start).blinkLine();
            });
        });
    }
}

$(document).ready(function () {
    var updateExpanded = function () {
        $('.expandLink.expanded').updateOffset();
    };

    $(window).scroll(updateExpanded);
    $(window).resize(updateExpanded);
    $('.expandLink').click(function () {
        $(this).toggleExpandCode();
        return false;
    });
    setUpSymbolicInfo();
    linkToCode();
});
