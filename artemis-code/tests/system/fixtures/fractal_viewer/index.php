<!DOCTYPE html "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
    <meta http-equiv="content-type" content="text/html; charset=utf-8"/>
    <title>Chrome Canopy</title>
    <link rel="stylesheet" href="style.css" type="text/css" />
	<script type="text/javascript" src="js/the_bones.js"></script>
	<script type="text/javascript" src="js/Vec2.js"></script>
	<script type="text/javascript" src="js/Rect2.js"></script>
	<script type="text/javascript" src="js/Brush.js"></script>
    <script type="text/javascript" src="js/Leaf.js"></script>
    <script type="text/javascript" src="js/the_meat.js"></script>
    <script type="text/javascript" src="js/Branch.js"></script>
	<script type="text/javascript" src="js/the_ui.js"></script>
	<script type="text/javascript" src="js/lib/jquery-1.3.js"></script>




</head>
<body onload="justInit();">
    <div id="my_container" style="display: none;">
        <canvas id="my_canvas"></canvas>
        <div id="control">
            <div>
                <a id="tog_play" class="play" href="#" onclick="toggle('play');">play</a>
            </div>
            <div>
                <a id="tog_flower" class="toggle" href="#" onclick="toggle('flower');">bloom</a>
                <a id="tog_mutate" class="toggle" href="#" onclick="toggle('mutate');">mutate</a>
            </div>
            <div>
                <a id="reset" href="#" onclick="reset();">new</a>
            </div>
            <div class="left">
                <a id="tog_about" class="toggle" href="#" onclick="toggle('about');">about</a>
            </div>
        </div>
    </div>
    <div id="about" style="display: none;">
        <div class="badge">
            <a href="http://chromeexperiments.com"><img src="img/badge.png" width="140" height="72" /></a>
        </div>
        <h1>Chrome Canopy</h1>
        <p>
            ..is a fractal zoomer. Press play to start falling. Click to go faster. You'll need a web browser with a fast JavaScript engine like <a href="http://www.google.com/chrome">Google Chrome</a>, <a href="http://www.apple.com/safari">Safari</a> or <a href="http://www.mozilla.com/firefox">Firefox</a>.
        </p>
        <ul>
            <li><span class="key">space / p</span> &mdash; play / pause</li>
            <li><span class="key">n</span> &mdash; make a new tree</li>
            <li><span class="key">m</span> &mdash; toggle mutuation</li>
            <li><span class="key">b</span> &mdash; toggle bloom</li>
            <li><span class="key">a</span> &mdash; show / hide this about box</li>
        </ul>
        <p>
            Designed by <a href="http://onecm.com">Ryan Alexander</a>
        </p>
    </div>
</body>
</html>
