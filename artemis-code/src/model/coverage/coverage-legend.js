
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
    if(turnOn){
        $(selector).css('background', colour);
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
                    $(this).css('background', '#EEEEEE');
                }else{
                    $(this).css('background', '#FFFFFF');
                }
            });
        }else{
            $(selector).css('background', 'none');
        }
    }
}

