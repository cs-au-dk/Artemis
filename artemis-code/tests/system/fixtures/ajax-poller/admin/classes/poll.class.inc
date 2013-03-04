<?php

/**
* Class for the poll
**/

class poll
{
	var $ID;
	var $pollerTitle;
	
	
	function poll()
	{
		$this->ID = "";
		$this->pollerTitle = "";
	}
			
	function setId($id)
	{
		$this->ID = $id;
	}
	
	function getDataById($id)
	{
		$res = mysql_query("select * from poller where ID='$id'");
		if($inf = mysql_fetch_array($res)){
			$this->ID = $inf["ID"];
			$this->pollerTitle = $inf["pollerTitle"];
		}		
		
	}
	
	/* This method returns poller options as an associative array */
	
	function getOptionsAsArray()
	{
		$retArray = array();
		$res = mysql_query("select * from poller_option where pollerID='".$this->ID."' order by pollerOrder");
		while($inf = mysql_fetch_array($res)){
			$retArray[$inf["ID"]] = array($inf["optionText"],$inf["pollerOrder"]);
		}	
		return $retArray;
		
	}
	
	/* This method returns number of votes as an associative array */
	function getVotesAsArray()
	{
		$retArray = array();
		$res = mysql_query("select v.optionID,count(v.ID) as countVotes from poller_vote v,poller_option o where v.optionID = o.ID and o.pollerID = '".$this->ID."' group by v.optionID");
		while($inf = mysql_fetch_array($res)){
			$retArray[$inf["optionID"]] = $inf["countVotes"];		
			
		}		
		return $retArray;
	}	
	
	/* Create new poller and return ID of new poller */
	
	function createNewPoller($pollerTitle)
	{
		global $db;
		$res = mysql_query("insert into poller(pollerTitle)values('$pollerTitle')") or die(mysql_error());
		$this->ID = mysql_insert_id();
		return $this->ID;
	}
	
	/* Add poller options */
	
	function addPollerOption($optionText,$pollerOrder)
	{
		mysql_query("insert into poller_option(pollerID,optionText,pollerOrder)values('".$this->ID."','".$optionText."','".$pollerOrder."')") or die(mysql_error());
		return mysql_insert_id();		
	}
	
	/* Delete a poll, options in the poll and votes */
	function deletePoll($pollId)
	{
		mysql_query("delete from poller where ID='$pollId'");
		$res = mysql_query("select * from poller_option where pollerID='".$pollId."'");
		while($inf = mysql_fetch_array($res)){
			mysql_query("delete from poller_vote where optionID='".$inf["ID"]."'");
			mysql_query("delete from poller_option where ID='".$inf["ID"]."'");
		}		
	}
	/* Updating poll title */
	function setPollerTitle($pollerTitle)
	{
		mysql_query("update poller set pollerTitle='$pollerTitle' where ID='".$this->ID."'");
	}
	
	/* Update option label */
	function setOptionData($newText,$order,$optionId)
	{
		mysql_query("update poller_option set optionText='".$newText."',pollerOrder='$order' where ID='".$optionId."'");		
	}
	
	/* Get position of the last option, i.e. to append a new option at the bottom of the list */
	
	function getMaxOptionOrder()
	{
		$res = mysql_query("select max(pollerOrder) as maxOrder from poller_option where pollerID='".$this->ID."'") or die(mysql_error());
		if($inf = mysql_fetch_array($res)){
			return $inf["maxOrder"];
		}
		return 0;		
	}
	
	/* Return order of poller options as array */
}




?>