<?

require_once('magpierss/rss_fetch.inc');


define("MAGPIE_CACHE_AGE",600);	// Cache time in seconds- 10 minutes

if(!isset($_GET['rssURL'])){
	die("No RSS url given");
}

if(!file_exists("cache"))mkdir("cache",0775);

$rss = fetch_rss($_GET['rssURL']);

$rssItems = $rss->items;	// News items
$maxRssItems = $_GET['maxRssItems']; 	// Maximum number of RSS news to show.

echo $rss->channel['title']."\n";	// Site title
echo min($maxRssItems,count($rssItems))."\n";	// Number of news

$outputItems = array();	// Creating new array - this items holds the data we send back to the client

for($no=0;$no<count($rssItems);$no++){
	#if(!isset($rssItems[$no]["pubdate"]))$rssItems[$no]["pubdate"]=$no;
	if(!isset($rssItems[$no]["description"]))$rssItems[$no]["description"]=" ";

	$key = $rssItems[$no]["date_timestamp"].(5000 - $no);
	$outputItems[$key] = array(
		"title"=>$rssItems[$no]["title"],
		"date_timestamp"=>$rssItems[$no]["date_timestamp"],
		"pubdate"=>$rssItems[$no]["pubdate"],
		"description"=>$rssItems[$no]["description"],
		"link"=>$rssItems[$no]["link"],
		"category"=>$rssItems[$no]["category"]);	
}


ksort($outputItems,SORT_NUMERIC);	// Sorting items from the key
$outputItems = array_reverse($outputItems);	// Reverse array so that the newest item appear first

$countItems = 0;

foreach($outputItems as $key=>$value){	// Output items - looping throught the array $outputItems
	echo "\n\n";	
	echo preg_replace("/[\r\n]/"," ",$value["title"])."##";	// Title
	echo date("Y-m-d H:i:s",$value["date_timestamp"])."##";	// Date
	echo preg_replace("/[\r\n]/"," ",$value["description"])."##";	// Description
	echo preg_replace("/[\r\n]/"," ",$value["link"])."##";	// Link
	$countItems++;
	if($countItems>=$maxRssItems)exit;	

}
exit;
?>