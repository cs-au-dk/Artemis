GET_PAGE_URL = 'http://localhost:8000/ajax/get_page/';
DELETE_URL = 'http://localhost:8000/ajax/delete/';
CHECKIN_URL = 'http://localhost:8000/ajax/checkin/';
ATTENDEE_URL = 'http://localhost:8000/ajax/attendee/';
SEARCH_URL = 'http://localhost:8000/ajax/search/';

function goto_page(id, query) {
    q = '';
    if (query) {
        q = query;
    }

    jQuery.ajax(GET_PAGE_URL + '?page=' + id + '&query=' + q, {
        'dataType': 'json',
        'success': function(result) {
            populate_table(result);
        },
    });    
}

function populate_table(attendees) {
    table = $('#attendees')
    table.html('');
    
    for (i = 0; i < attendees.length; i++) {
        id = attendees[i]['id'];
        name = attendees[i]['name'];
        email = attendees[i]['email'];
        department = attendees[i]['department'];
        paid = attendees[i]['paid'];
        checkedin = attendees[i]['checkedin'];
        
        style = ''
        if (checkedin) {
            style = ' style="background-color: #B6EDB8;"';
        }   
        
        ahtml = '<tr id="row' + id + '"' + style + '>';
        ahtml += '<td><b>' + name + '</b> - ' + email + '<br/>' + department + '</td>';
        ahtml += '<td><a href="#" onclick="info(' + id + ')">[info]</a> ';
        ahtml += '<a href="#" onclick="checkin(' + id + ')">[checkin]</a> ';
        ahtml += '<a href="#" onclick="del(' + id + ')">[delete]</a>';
        ahtml += '</tr>';
        
        table.append(ahtml);
    }
}

function populate_control(pages, query) {
    control = $('#control');
    control.html('');
    
    q = ''
    if (query) {
        q = ", '" + query + "'";
    }
    
    for (i = 1; i <= pages; i++) {
        page_link = '<a href="#" onclick="goto_page(' + i + q + ');">' + i + '</a> ';
    
        control.append(page_link);
    }
}

function info(id) {
    jQuery.ajax(ATTENDEE_URL + '?id=' + id, {
        'dataType': 'json',
        'success': function(result) {
            id = result['id'];
            name = result['name'];
            email = result['email'];
            department = result['department'];
            paid = result['paid'];
            checkedin = result['checkedin'];
            
            attendee_info = '<h3>' + name + '</h3>';
            attendee_info += '<p>' + department + ' - ' + email + '</p>';
            attendee_info += '<p>Paid: ' + paid + ' &nbsp;&nbsp;&nbsp;';
            attendee_info += 'Checked in: ' + checkedin + '</p>';
        
            $('#infobox').html(attendee_info);
        },
    });
};

function del(id) {
    jQuery.ajax(DELETE_URL + '?id=' + id, {
        'dataType': 'json',
        'success': function(result) {
            $('#row' + id).fadeOut();
        },
    });
};

function checkin(id) {
    jQuery.ajax(DELETE_URL + '?id=' + id, {
        'dataType': 'json',
        'success': function(result) {
            $('#row' + id).css("background-color", "#B6EDB8");
        },
    });
};

$(function() {
    goto_page(1);
    populate_control(10);
    
    $('#searchbutton').bind('click', function() {
        jQuery.ajax(SEARCH_URL + '?query=' + $('#searchbox')[0].value, {
            'dataType': 'json',
            'success': function(result) {
                populate_table(result['attendees']);
                populate_control(result['pages'], $('#searchbox')[0].value);
            },
        });
    });
});