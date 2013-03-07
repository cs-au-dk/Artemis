<?php
/* Admin tool for the Ajax poller script */

error_reporting(E_ALL);
ini_set('error_reporting', E_ALL);
ini_set("display_errors", "1");

include_once("dbConnect.php");
include_once("classes/poll.class.inc");


?>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd">
<html>
<head>
	<title>Poller admin</title>
	<link rel="stylesheet" href="css/admin.css" type="text/css">
	<script type="text/javascript">
	function moveDown(optionId)
	{
		var el = document.getElementById('option' + optionId);
		if(el.nextSibling){
			var nextObj = el.nextSibling;
			var inputsNext = nextObj.getElementsByTagName('INPUT');
			
			var nextOrder = false;
			for(var no=0;no<inputsNext.length;no++){
				if(inputsNext[no].id.indexOf('existing_pollOrder')>=0)nextOrder = inputsNext[no];	
			}
			var inputsThis = el.getElementsByTagName('INPUT');
			var thisOrder = false;
			for(var no=0;no<inputsThis.length;no++){
				if(inputsThis[no].id.indexOf('existing_pollOrder')>=0)thisOrder = inputsThis[no];	
			}			
			var tmpValue = nextOrder.value;
			nextOrder.value = thisOrder.value;
			thisOrder.value = tmpValue;
			el.parentNode.insertBefore(el.nextSibling,el);
		}
		
	}
	</script>
	
</head>
<body>
<form action="<?php echo $_SERVER['PHP_SELF']; ?>" method="post">

<?php

$id = "";
if(isset($_POST['ID']))$id = $_POST['ID'];	// Opened by form submission
if(isset($_GET['id']))$id = $_GET['id'];	// Opened from list
if(isset($_POST['cancel']))$id = "";

if(isset($_POST['delete'])){
	$pollObj = new poll();
	$pollObj->deletePoll($_POST['ID']);	
	
}

if(isset($_POST['save'])){
	$pollObj = new poll();
	
	if(empty($_POST['ID'])){ // new poll
		if(isset($_POST['pollerTitle'])){
			$id = $pollObj->createNewPoller($_POST['pollerTitle']);
			echo "ID: ".$id;
			for($no=0;$no<count($_POST['pollOption']);$no++){
				if(!empty($_POST['pollOption'][$no])){
					$pollObj->addPollerOption($_POST['pollOption'][$no],$no);	
				}	
			}
			

			
		}else{
			$error_message = "Poller title is missing";
		}
	}else{	// Update existing poll
		$pollObj->setId($_POST['ID']);	// Setting id
		if(isset($_POST['pollerTitle']))$pollObj->setPollerTitle($_POST['pollerTitle']);
		foreach($_POST['existing_pollOption'] as $key=>$value){
			if(!empty($_POST['existing_pollOption'][$key]))	$pollObj->setOptionData($_POST['existing_pollOption'][$key],$_POST['existing_pollOrder'][$key],$key);
		}
		
		$maxOrder = $pollObj->getMaxOptionOrder() + 1;
		for($no=0;$no<count($_POST['pollOption']);$no++){
			if(!empty($_POST['pollOption'][$no])){
				$pollObj->addPollerOption($_POST['pollOption'][$no],$maxOrder);	
				$maxOrder++;
			}	
		}
					
	}
		
	
	
	
}

// Show a list of all the polls
if(!isset($_POST['new']) && empty($id)){
	?>
	<fieldset>
		<table>
			<tr>
				<td><input type="submit" name="new" value="New" class="formButton"></td>
			</tr>
		</table>
	</fieldset>	
	<fieldset>
		<legend>All polls</legend>
		<table>
		<?php	
		$res = mysql_query("select * from poller order by pollerTitle");
		while($inf = mysql_fetch_array($res)){
			echo "<tr><td><a href=\"".$_SERVER['PHP_SELF']."?id=".$inf["ID"]."\">".$inf["pollerTitle"]."</a></td></tr>";
		}
		?>
		</table>
	</fieldset>
	<?php
}


/***
* Show a new poll or edit a poll
***/

if(isset($_POST['new']) || !empty($id))
{

	$pollObj = new poll();
	if(!empty($id)){
		$pollObj->getDataById($id);		
		$pollerOptions = $pollObj->getOptionsAsArray();
		$votes = $pollObj->getVotesAsArray();
	}else{
		$pollerOptions = array();
		$votes = array();
	}

	
	?>
	
	<input type="hidden" name="ID" value="<?php echo $pollObj->ID; ?>">
	<fieldset>
		<table>
			<tr>
				<td><input type="submit" name="save" value="Save" class="formButton"></td>
				<td><input type="submit" name="cancel" value="Cancel" class="formButton"></td>
				<?php
				if(!empty($id)){
					?>
					<td><input type="submit" name="delete" value="Delete" onclick="return confirm('Click OK to delete this poll')" class="formButton"></td>
					<?php					
				}
				?>
			</tr>
		</table>
	</fieldset>
	<fieldset>
		<legend>Add/Edit poller</legend>
		<table>
			<tr>
				<td><label for="pollerTitle">Poller title:</label></td>
				<td><input type="text" size="60" maxlength="55" id="pollerTitle" name="pollerTitle" value="<?php echo $pollObj->pollerTitle; ?>"></td>
			</tr>
		</table>
		<table width="100%">
			<tr>
				
				<?php
				if(!isset($_POST['new'])){
					?>
					<th>Option</th>
					<th>Votes</th>
					<th>Move down</th>
					<?php
				}else{
					?>
					<th>Options</th>
					<?php
				}
				?>
			</tr>
			<?php
			foreach($pollerOptions as $key=>$value){
				echo "<tr id=\"option$key\">";
				echo "<td><input type=\"text\" maxlength=\"255\" size=\"50\" name=\"existing_pollOption[$key]\" value=\"".$pollerOptions[$key][0]."\"></td>";
				echo "<td>".(isset($votes[$key])?$votes[$key]:0)."</td>";
				echo "<input type=\"hidden\" id=\"existing_pollOrder[$key]\" name=\"existing_pollOrder[$key]\" value=\"".$pollerOptions[$key][1]."\">";
				echo "<td><a href=\"#\" onclick=\"moveDown('$key');return false\">Move down</a></td>";
				echo "</tr>\n";				
			}
			
			if(empty($id)){
				$countInputs = 10;		
			}else{
				$countInputs = 3;
				echo "<tr><td><b>New options</td></tr>";
				
			}
			for($no=0;$no<$countInputs;$no++){
				echo "<tr><td><input type=\"text\" maxlength=\"255\" size=\"50\" name=\"pollOption[$no]\"></td></tr>\n";					
			}	
				
			?>							
		</table>		
	</fieldset>	
	
	<?php	
}

?>
</form>
</body>
</html>