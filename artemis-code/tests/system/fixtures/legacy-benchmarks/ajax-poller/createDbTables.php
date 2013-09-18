<?php

/* 	This is the SQL that creates the default tables used in the poller script from www.dhtmlgoodies.com	*/

//SQL that creates the tables needed in this demo

require_once dirname(__FILE__).'/dbConnect.php';

/** @var $connection SQLite3 */
$connection->query("drop table poller");
$connection->query("drop table poller_vote");
$connection->query("drop table poller_option");

$connection->query("create table poller(pollerTitle varchar(255))") or die($connection->lastErrorMsg());

$connection->query("create table poller_vote(
optionID int(11),
ipAddress varchar(255))") or die($connection->lastErrorMsg());

$connection->query("create table poller_option(
pollerID int(11),
optionText varchar(255),
pollerOrder int,
defaultChecked char(1) default 0)") or die($connection->lastErrorMsg());


$connection->query("insert into poller(pollerTitle)values('How would you rate this script?')");

$connection->query("insert into poller_option(pollerID,optionText,pollerOrder,defaultChecked)values('1','Excellent','1','1')");
$connection->query("insert into poller_option(pollerID,optionText,pollerOrder)values('1','Very good','2')");
$connection->query("insert into poller_option(pollerID,optionText,pollerOrder)values('1','Good','3')");
$connection->query("insert into poller_option(pollerID,optionText,pollerOrder)values('1','Fair','3')");
$connection->query("insert into poller_option(pollerID,optionText,pollerOrder)values('1','Poor','4')");
?>



