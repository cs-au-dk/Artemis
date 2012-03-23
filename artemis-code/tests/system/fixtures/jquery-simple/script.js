$(function() {

    /** JQUERY INSTRUMENTATION **/
    old_event_add = jQuery.event.add
   
    function __jquery_event_add__(elem, types, handler, data, selector) {
        return old_event_add(elem, types, handler, data, selector);
    }

    jQuery.event.add = __jquery_event_add__
    /** END JQUERY INSTRUMENTATION **/

    $('#invokepoint').click(function() {
        alert("clicked");
    })
});
