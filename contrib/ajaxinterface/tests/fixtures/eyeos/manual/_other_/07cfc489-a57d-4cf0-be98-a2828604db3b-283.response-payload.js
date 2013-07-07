//
//  iana.org Javascript Code
//
//  The general aim is for these to be auxiliary functions, which
//  if they fail, will gracefully degrade in the user's browser.
//  No IANA page should rely on JavaScript's existence, rather, it
//  should add optional additional functionality, or presentation
//  assistance.
//
//


//  HOMEBREW FUNCTIONS
//

var dfilt = 0;
var tfilt = 0;
var sfilt = '';

function insertNavigationHelper(el, filters) {

	var html = "";
	
	// Clear filter

        html = html + "<a href=\"#\" onclick=\"filtersearchclear();\">All</a>&nbsp;"

	for (var f=0; f<filters.length; f++) {
		filter = filters[f]


		// Alphabetical filter

		if (filter == "alpha") {
	
			for (var i=0; i<26; i++) {
				var letter = String.fromCharCode ( i+65 );
				html = html + "<a href=\"#\" class=\"iana-table-nav-cell\" onclick=\"filteralpha("+(i+1)+");\" id=\"ianatfa-"+(i+1)+"\">"+letter+"</a>&nbsp;";
			}
			html = html + "&nbsp;"
		}

		// Class filter

		else if (filter == "tldtype") {
	
			html = html + "<a href=\"#\" onclick=\"filtertype(1)\" id=\"ianatfc-1\" class=\"iana-table-nav-cell\">ccTLDs</a>&nbsp;";
			html = html + "<a href=\"#\" onclick=\"filtertype(2)\" id=\"ianatfc-2\" class=\"iana-table-nav-cell\">gTLDs</a>&nbsp;";
			html = html + "<a href=\"#\" onclick=\"filtertype(3)\" id=\"ianatfc-3\" class=\"iana-table-nav-cell\">IDNs</a>&nbsp;";
			html = html + " &nbsp;"
		}

		// Input filter

		else if (filter == "search") {
	
			html = html + "<input id=\"table-search\" onkeyup=\"filterterm()\">&nbsp;";
		}

	}

	// Clear filters

	html = html + "<a href=\"#\" onclick=\"filtersearchclear();\"><img alt=\"Reset search\" id=\"iana-table-icon\" src=\"/_img/iana-clear-search.png\"></a>";

	$(el).innerHTML = html;
	Element.addClassName(el, "iana-table-navigation")

}

function insertIDNHelper() {
}

function refiltertable() {

	var rows = $$('.iana-table tbody tr');
	var matchcount = 0
	for (var i=0; i<rows.length; i++) {
		var show = 1
		if ((dfilt > 0) && !Element.hasClassName(rows[i], "iana-group-"+dfilt)) {
			show = 0
		}
		if ((tfilt > 0) && !Element.hasClassName(rows[i], "iana-type-"+tfilt)) {
			show = 0
		}
		if (sfilt != '') {
			matches = 0
			var cols = Element.childElements(rows[i])
			for (var j=0; j<cols.length; j++) {
				var text = cols[j].innerHTML.toLowerCase()
				if (text.indexOf(sfilt.toLowerCase()) != -1) {
					matches = 1
				}
			}
			if (matches == 0) {
			show = 0
			}
		}
		if (show == 1) {
			Element.show(rows[i]);
			matchcount = matchcount + 1;
		} else {
			Element.hide(rows[i]);
		}
	}
	var $n = $('iana-table-notice');
	if ($n) {
		$n.remove();
	}
	if (matchcount == 0) {
		var notice = $E({tag: 'div', id: 'iana-table-notice', children: ["There are no entries that match."]});
		$('iana-tld-nav').appendChild(notice);	
	} 
}
	
	function resetbuttons() {
		for (var i=1; i<27; i++) {
			if (i == dfilt) {
				Element.addClassName('ianatfa-'+i, "iana-table-nav-hl"); 
			} else {
				Element.removeClassName('ianatfa-'+i, "iana-table-nav-hl"); 
			}
		}
		for (var i=1; i<3; i++) {
			if (i == tfilt) {
				Element.addClassName('ianatfc-'+i, "iana-table-nav-hl");
			} else {
				Element.removeClassName('ianatfc-'+i, "iana-table-nav-hl");
			}
		}
	}
	
	function filteralpha(i) { dfilt = i; refiltertable(); resetbuttons() }
	function filtertype(i) { tfilt = i; refiltertable(); resetbuttons() }
	function filterterm() { sfilt = $F($('table-search')); refiltertable() }
	function filtersearchclear() { $('table-search').clear(); dfilt=0; tfilt=0; sfilt = ''; refiltertable(); resetbuttons() }

	function unsharpenDiv(divs,cornerRadius) {
	/*
		Adds rounded corners to a div, with a specified radius.
	*/	

		if (typeof(divs) == 'string') {
			divs = [divs];
		}

		for (var i=0; i<divs.length; i++) {
			var divName = divs[i];
			var settings = { tl: { radius: cornerRadius}, tr: { radius: cornerRadius}, bl: { radius: cornerRadius}, br: { radius: cornerRadius}, antiAlias: true, autoPad: true, validTags: ["div"] };
			var framecorners = new curvyCorners(settings, divName); 
			framecorners.applyCornersToAll();
		}
	}

	function makeHoverTable(tableName) {
	/*
		Makes entire table rows clickable links, if the first column contains
		a link.
	*/

		var rows = $$('#'+tableName+' tbody tr');
        	for (var i=0; i<rows.length; i++) {
			var links = rows[i].getElementsByTagName('a');
			if (links[0].href) {
				rows[i].onmouseover = function() { $(this).addClassName('iana-table-hover'); };
				rows[i].onmouseout = function() { $(this).removeClassName('iana-table-hover'); };
				eval("rows[i].onclick = function() { location.href = '"+links[0].href+"' };");
         	       }
		}
	}

	function equaliseHeights(els) {

		var height = 0;
		for (var i=0; i<els.length; i++) {
			el = $(els[i]);
			if (el.offsetHeight) {	
				elheight = el.offsetHeight;
			} else {
				elheight = el.style.pixelHeight;
			}
			if (elheight > height) {
				height = elheight;
			}
		}
		for (var i=0; i<els.length; i++) {
			el = $(els[i]);
			el.style.height = height+'px';
		}
	}	

//  THIRD PARTY FUNCTIONS
//

function $E(data) {

        /*
            Convenience wrapper for document.createElement
            From http://www.arantius.com/article/dollar+e
        */

        var el;
        if ('string'==typeof data) {
                el=document.createTextNode(data);
        } else {
                //create the element
                el=document.createElement(data.tag);
                delete(data.tag);

                //append the children
                if ('undefined'!=typeof data.children) {
                        if ('string'==typeof data.children ||
                                'undefined'==typeof data.children.length
                        ) {
                                //strings and single elements
                                el.appendChild($E(data.children));
                        } else {
                                //arrays of elements
                                for (var i=0, child=null; 'undefined'!=typeof (child=data.children[i]); i++) {
                                        el.appendChild($E(child));
                                }
                        }
                        delete(data.children);
                }

                //any other data is attributes
                for (attr in data) {
                        el[attr]=data[attr];
                }
        }

        return el;
}
