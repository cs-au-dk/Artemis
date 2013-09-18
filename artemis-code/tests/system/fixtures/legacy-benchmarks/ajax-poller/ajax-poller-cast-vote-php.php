<?php

if(isset($_GET['pollId'])){
	
	require_once("dbConnect.php");

	$optionId = false;
	
	if(isset($_GET['optionId'])){
		$optionId = $_GET['optionId'];
		$optionId = preg_replace("/[^0-9]/si","",$optionId);
	}
	$pollId = $_GET['pollId'];
	$pollId = preg_replace("/[^0-9]/si","",$pollId);
	

			
	// Insert new vote into the database
	// You may put in some more code here to limit the number of votes the same ip adress could cast.

    /** @var $connection SQLite3 */
	if($optionId) $connection->query("insert into poller_vote(optionID,ipAddress)values('".$optionId."','".getenv("REMOTE_ADDR")."')");
	
	// Returning data as xml
	
	echo '<?xml version="1.0" ?>';
	
	$res = $connection->query("select pollerTitle, rowid as ID from poller where rowid='".$pollId."'");
	if($inf = $res->fetchArray()){
		echo "<pollerTitle>".$inf["pollerTitle"]."</pollerTitle>\n";
		
		$resOptions = $connection->query("select rowid AS ID,optionText from poller_option where pollerID='".$inf["ID"]."' order by pollerOrder") or die($connection->lastErrorMsg());
		while($infOptions = $resOptions->fetchArray()){
			echo "<option>\n";
			echo "\t<optionText>".$infOptions["optionText"]."</optionText>\n";					
			echo "\t<optionId>".$infOptions["ID"]."</optionId>\n";					
			
			$resVotes = $connection->query("select count(optionID) as c from poller_vote where optionID='".$infOptions["ID"]."'");
			if($infVotes = $resVotes->fetchArray()){
				echo "\t<votes>".$infVotes["c"]."</votes>\n";
			}										
			echo "</option>";				
			
		}				
	}
	exit;

}else{
	echo "No success";
	
}

?>