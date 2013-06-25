
/* Use the legend to toggle the different line/statement colourings on or off. */

$(document).ready(function(){
    $('#legend > ul > li').each(function(idx){
        $(this).prepend('<input type="checkbox" checked="true" class="' + $(this).attr('class') + '" style="margin: 5px" ></input>');
    });
    
    $('#legend input').on('change', function(e){
        var turnOn = this.checked;
        
        // TODO: It's not ideal that all these colours are hard-coded here.
        // Ideally we could take them directly from the CSS or something?
        
        if($(this).hasClass('covered')){
            toggleBackground(this.checked, 'pre > ol > li.covered', '#FFEEB2', true);
            return;
        }
        
        if($(this).hasClass('symCovered')){
            toggleBackground(this.checked, 'pre > ol > li.symCovered', '#E29C1D', true);
            return;
        }
        
        if($(this).hasClass('stmtCovered')){
            toggleBackground(this.checked, 'pre > ol > li.covered > span.covered, pre > ol > li.symCovered > span.covered', '#FF6868', false);
            return;
        }
        
        if($(this).hasClass('symStmtCovered')){
            toggleBackground(this.checked, 'pre > ol > li.symCovered > span.symCovered, pre > ol > li.covered > span.symCovered', '#FF004E', false);
            return;
        }
        
        if($(this).hasClass('linkedLine')){
            toggleBackground(this.checked, 'pre > ol > li.linkedLine', '#66FF99', true);
            return;
        }
    });
});


function toggleBackground(turnOn, selector, colour, isAWholeLine){
    /*
     * We need to set !important on (some of) these rules, as that is used in some of the styles we are overriding
     * (specifically the symbolic coverage rule). However, jQuery's .css() method does not support this (at least in 
     * firefox, I have heard it works in Chrome), so we set the style attribute instead. 
     * This will overwrite any existing style!
     */
    if(turnOn){
        $(selector).attr('style', 'background: ' + colour + ' !important');
    }else{
        // If the element is a li and has a line marker which is odd, then mark it with a grey background, otherwise white.
        // If the element is not a whole line, then just remove any background.
        if(isAWholeLine){
            $(selector).each(function(idx){
                if($(this).hasClass('L1') || 
                        $(this).hasClass('L3') || 
                        $(this).hasClass('L5') || 
                        $(this).hasClass('L7') || 
                        $(this).hasClass('L9')){
                    $(this).attr('style', 'background: #EEEEEE !important');
                }else{
                    $(this).attr('style', 'background: #FFFFFF !important');
                }
            });
        }else{
            $(selector).attr('style', 'background: none !important');
        }
    }
}

