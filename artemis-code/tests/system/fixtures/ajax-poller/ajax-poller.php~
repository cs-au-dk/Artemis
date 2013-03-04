<?php
include_once("dbConnect.php");
?>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd">
<HTML>
<HEAD>
	<?php
	@include($_SERVER['DOCUMENT_ROOT']."/config/metatags.inc");
	?>	
	<title>Ajax poller</title>
	<style type="text/css">

	
	
	/* DEMO CSS */
	img{
		border:0px;
	}
	
	#mainContainer{
		width:760px;
		margin:0 auto;
		text-align:left;
		background-color:#FFF;
		
	}

	#mainContent{
		padding:10px;
	}
	
	.clear{
		clear:both;
	}
	</style>
	<link rel="stylesheet" href="css/ajax-poller.css" type="text/css">
	<script type="text/javascript" src="js/ajax.js"></script>
	<script type="text/javascript" src="js/ajax-poller.js">	</script>

</HEAD>
<BODY>

<form action="<?php echo $_SERVER['PHP_SELF']; ?>" onsubmit="return false" method="post" name="artemis">
<div id="mainContainer">
	<div id="mainContent">
	
		<?php
		$pollerId = 1;	// Id of poller
		?>
		<!-- START OF POLLER -->
		<div class="poller">
		
			<div class="poller_question" id="poller_question<?php echo $pollerId; ?>">
			<?php			
			
			
			// Retreving poll from database
			$res = mysql_query("select * from poller where ID='$pollerId'");	
			if($inf = mysql_fetch_array($res)){
				echo "<p class=\"pollerTitle\">".$inf["pollerTitle"]."</p>";	// Output poller title
				
				$resOptions = mysql_query("select * from poller_option where pollerID='$pollerId' order by pollerOrder") or die(mysql_error());	// Find poll options, i.e. radio buttons
				$ii = 0;
				while($infOptions = mysql_fetch_array($resOptions)){
					$ii++;
					if($infOptions["defaultChecked"])$checked=" checked"; else $checked = "";
					echo "<p class=\"pollerOption\"><input$checked type=\"radio\" value=\"".$infOptions["ID"]."\" name=\"vote[".$inf["ID"]."]".$ii."\" id=\"pollerOption".$infOptions["ID"]."\"><label for=\"pollerOption".$infOptions["ID"]."\" id=\"optionLabel".$infOptions["ID"]."\">".$infOptions["optionText"]."</label></p>";	
			
				}
			}			
			?>			
			<a href="#" onclick="castMyVote(<?php echo $pollerId; ?>,document.forms[0])"><img src="images/vote_button.gif"></a>
			</div>
			<div class="poller_waitMessage" id="poller_waitMessage<?php echo $pollerId; ?>">
				Getting poll results. Please wait...
			</div>
			<div class="poller_results" id="poller_results<?php echo $pollerId; ?>">
			<!-- This div will be filled from Ajax, so leave it empty --></div>
		</div>
		<!-- END OF POLLER -->
		<script type="text/javascript">
		if(useCookiesToRememberCastedVotes){
			var cookieValue = Poller_Get_Cookie('dhtmlgoodies_poller_<?php echo $pollerId; ?>');
			if(cookieValue && cookieValue.length>0)displayResultsWithoutVoting(<?php echo $pollerId; ?>); // This is the code you can use to prevent someone from casting a vote. You should check on cookie or ip address
		
		}
		</script>
		
		<p>This is an example of a poll script. It uses Ajax(Asyncron Javascript And XML) to send your vote to the server. Ajax is also used to return the results from this poll to your browser.</p>
		<p>In this demo, I haven't limited the number of votes per user. This is something you can implement by setting the Javascript variable
		useCookiesToRememberCastedVotes to true in the script or by implementing your own method.</p>
	</div>
	<div class="clear"></div>
</div>
</form>

</BODY>
</HTML>