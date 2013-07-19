$(function() {

	// JQUERY INSTRUMENTATION
	old_event_add = jQuery.event.add

	function __jquery_event_add__(elem, types, handler, data, selector) {
		return old_event_add(elem, types, handler, data, selector);
	}

	jQuery.event.add = __jquery_event_add__
	// JQUERY INSTRUMENTATION END

	var user; // current user, set after authentication
	var stage; // applicant/supervisor/grantholder/supervisorgrantholder/completed
	var countries; // loaded from countries.json
	var groups; // loaded from groups.json
	var rates = {}; // map from country to daily allowance rate
	var staff = {}; // map from staff username to real name
	
	// general Ajax error handler
	$(document).ajaxError(function(event, jqxhr, settings, exception) {
		if (settings.url == 'travel/currentUser') {
			$('.caption,#application').hide();
			$('#authorizationFailed').show();
		} else {
			alert('Unable to contact server :-(\n ' +
				  (exception ? '\nMessage: ' + exception : ''));
		}
	});

	// load data and authenticate user, then call ready
	$.getJSON('groups.json', function(g) {  
		groups = g;
		$.getJSON('countries.json', function(c) { 
			countries = c;
			$.getJSON('travel/currentUser', function(u) {
				user = u;
				var v = {};
				for (var i in groups) {
					var g = groups[i];					
					for (var i = 0; i < g.members.length; i++) 
						v[g.members[i]] = undefined;
					v[g.admin] = v[g.phdadmin] = v[g.csadmin] = undefined;
				}
				var t = [];
				for (var p in v)
					t.push(p);
				$.getJSON('travel/getUsers?usernames=' + JSON.stringify(t), function(users) {
					$.each(users, function(_, u) {
						staff[u.username] = u.name;
					});
					ready();
				});
			});
		});
	});
	
	function ready() {
		
		// add image checkboxes
		$("#supervisorApproved,#grantAdministratorApproved").change(function() {
			if (this.checked)
				$(this).prev().attr("src", "checked.png");
			else
				$(this).prev().attr("src", "unchecked.png");
		});
		
		// add countries to menu
		rates = {}; // map from country to daily allowance rate
		$('#countrySuggest').empty();
		for (var y in countries) {
			for (var x in countries[y]) {
				rates[x] = countries[y][x];
				$('#countrySuggest').append($('<option/>', {value: x, text: x}));
			}
		}
		
		// add grant holders
		var g = [];
		for (var i in groups) {
			var group = groups[i];
			for (var i = 0; i < group.members.length; i++) {
				var s = group.members[i];
				g.push({value: s, text: staff[s]});
			}
		}
		g.sort(function(a,b) {return a.text < b.text ? -1 : a.text > b.text ? 1 : 0;});
		for (var i = 0; i < g.length; i++)
			$('#grantHolder').append($('<option/>', g[i]));

		// add groups and supervisors to menus
		for (var i in groups) {
			var g = groups[i];
			$('#researchGroup').append($('<option/>', {value: g.name, text: g.name}).data('admin', g.admin));
			for (var j = 0; j < g.members.length; j++) {
				var member = g.members[j];
				$('#supervisor').append($('<option/>', {value: member, text: staff[member]}).data('group', g));
			}
		}

		// filter supervisor options based on group
		var prevGroup = '';
		function fillSupervisorList() {
			var group = $('#researchGroup').val();
			// remove those not belonging to the group
			$('#supervisor option').each(function(i, selected) {
				selected = $(selected);
				var hide = i > 0 && selected.data('group').name != group && group != '';
				// if the selected one is hidden, select the dummy number 0 instead
				if (hide && selected.is(':selected'))
					$('#supervisor').prop('selectedIndex', 0);
				// detach the hidden ones (not all browsers support hidden options)
				if (hide)
					selected.detach();
			});
			if (prevGroup != '') {
				// add the missing ones
				for (var i in groups) {
					var g = groups[i];
					if (g.name == group || (group == '' && prevGroup != g.name)) {
						for (var j in g.members) {
							var member = g.members[j];
							$('#supervisor').append($('<option/>', {value: member, text: staff[member]}).data('group', g));
						}
					}
				}
			}
			prevGroup = group;
		}
		$('#researchGroup').change(fillSupervisorList);

		// set country when selected in countrySuggest menu
		$('#countrySuggest').prop('selectedIndex', -1);
		$('#countrySuggest').change(function(event) {
			$('#destinationCountry').attr('value',$(this).val());
			$('#countrySuggest').prop('selectedIndex', -1);
		});

		// date pickers
		$('#travelStart').datepicker();
		$('#travelEnd').datepicker();
		$('#travelStart').change(function() {
			if ($('#travelEnd').val()=='')
				$('#travelEnd').attr('value',$(this).val());
		});

		// autofill days
		$('#travelStart,#travelEnd').change(function() {
			var from = $('#travelStart').datepicker('getDate');
			var to = $('#travelEnd').datepicker('getDate');
			if (from && to) {
				var days = Math.round((to.getTime() - from.getTime())/(1000*60*60*24)+1);
				if (days < 1)
					days = '';
				$('#days').attr('value',days);
			}
		});

		// autofill totalExpenses
		function recalculateTotal() {
			var total = 0;
			$('.expense').each(function() {
				total += parseInt($(this).val().replace(',','.')) || 0;
			});
			$('#totalExpenses').attr('value',total);
		}
		$('#travelExpenses,#registrationFee,#dailyExpenses,#hotelExpenses,#otherExpenses').change(recalculateTotal);

		// autofill dailyExpenses
		function recalculateDaily() {
			var rate = rates[$.trim($('#destinationCountry').val())] || 0;
			// TODO: if rates[$.trim($('#destinationCountry').val())] is undefined then allow the user to edit the allowance field? (need new field in data model)
			var daily = $('#receiveDailyAllowance').attr('checked') ? $('#days').val() * rate : '0';
			$('#dailyExpenses').attr('value', daily).change();
		}
		$('#travelStart,#travelEnd,#receiveDailyAllowance,#days,#destinationCountry,#countrySuggest').change(recalculateDaily);
		
		// select all text when a text field receives focus
		$('input[type=text]').focus(function() {
			$(this).select();
			$(this).mouseup(function() { // Chrome work-around
				$(this).unbind("mouseup");
				return false;
			});
		});

		// checkbox 'presenting' only allowed if purpose is participation
		$(':input[name=purpose]').change(function() {
			if ($(':input[name=purpose]:checked').val() != 'participation')
				$(':input[name=presenting]').attr('checked', false);
		});
		$(':input[name=presenting]').change(function() {
			if ($(this).is(':checked'))
				$(':input[name=purpose][value=participation]').attr('checked', true);
		});

		// show bigArea when status is selected and supervisor areas when status is student
		var open = false;
		function showBigArea(field) {
			if (!open) {
				$('.bigArea').slideDown(1000);
				open = true;
			}
			// supervisorArea not relevant for Faculty/adm.
			if (field.val() == 'faculty')
				$('.supervisorArea').slideUp('fast');
			else {
				$('.supervisorArea').slideDown();
				fillSupervisorList();
			}
			// phdArea only relevant forPhD
			if (field.val() != 'phd')
				$('.phdArea').slideUp('fast');
			else {
				$('.phdArea').slideDown();
			}
		}
		$(':input[name=status]').change(function() { showBigArea($(this)); });

		// default form submit handler does nothing
		$('form').submit(function() { return false; });

		// get application ID from the URL parameter
		function getParameterByName(name) {
			name = name.replace(/[\[]/, '\\\[').replace(/[\]]/, '\\\]');
			var regexS = '[\\?&]' + name + '=([^&#]*)';
			var regex = new RegExp(regexS);
			var results = regex.exec(window.location.href);
			if(results == null)
				return '';
			else
				return decodeURIComponent(results[1].replace(/\+/g, ' '));
		}
		$('#id').val(getParameterByName('id'));

		// load application data
		$.getJSON('travel/getApplication', { application: $('#id').val() }, function(data) {
            stage = data.stage;
			if (stage == 'completed')
				$('#continue').hide();
			
			if ($('#id').val() != '') {
				var checkedStatus = $(':input[name=status][value=' + data.status + ']');
				if (checkedStatus.length > 0)
					showBigArea(checkedStatus);
				checkedStatus.attr('checked', true);
			}
			$(':input[name=applicant]').val(data.applicant.name + ' (' + data.applicant.username +  ')');
			$(':input[name=date]').val(dateString(data.dateOfApplication));
			$('.smallArea').show();	
			if (data.source) {
				$(':input[name=source][value='+data.source.type+']').attr('checked', true);
				if (data.source.type === 'other') {
					$(':input[name=projectName]').val(data.source.projectName);
					$('#grantHolder option[value='+data.source.grantHolder.username+']').attr('selected', true);
				}
			}
			var selectedGroup = $('#researchGroup option[value="'+data.researchGroup+'"]');
			if (selectedGroup.length > 0) {
				fillSupervisorList();
			}
			selectedGroup.attr('selected', true);
			if (data.supervisor)
				$('#supervisor option[value='+data.supervisor.username+']').attr('selected', true);
			$(':input[name=destinationCity]').val(data.destinationCity);
			$(':input[name=destinationCountry]').val(data.destinationCountry);
			$(':input[name=travelStart]').val(dateString(data.travelStart));
			$(':input[name=travelEnd]').val(dateString(data.travelEnd));
			$(':input[name=days]').val(data.days);
			if (data.purpose) {
				$(':input[name=purpose][value='+data.purpose.type+']').attr('checked', true);
				if (data.purpose.type === 'participation' && data.purpose.presentation)
					$(':input[name=presenting]').attr('checked', true);
				if (data.purpose.type === 'guest')
					$(':input[name=guestName]').val(data.purpose.name);
				if (data.purpose.type === 'other')
					$(':input[name=otherPurpose]').val(data.purpose.text);
				$(':input[name=purposeDetails]').val(data.purpose.description);
			}
			$(':input[name=travelExpenses]').val(data.expenses.travelExpense);
			$(':input[name=registrationFee]').val(data.expenses.registrationFee);
			if (data.expenses.receiveDailyAllowance)
				$(':input[name=receiveDailyAllowance]').attr('checked', true);
			//$(':input[name=dailyExpenses]').val(data["dailyExpenses"]);
			$(':input[name=hotelExpenses]').val(data.expenses.hotelExpense);
			$(':input[name=otherExpensesDescription]').val(data.expenses.otherText);
			$(':input[name=otherExpenses]').val(data.expenses.otherExpense);
			//$(':input[name=totalExpenses]').val(data["totalExpenses"]);
			$(':input[name=recommendationSupervisor]').val(data.recommendationSupervisor);
			$(':input[name=remarks]').val(data.remarks);
			if (data.supervisorApproved) {
				var t = $(':input[name=supervisorApproved]');
				t.attr('checked', true).after('(' + data.supervisorApproved.name + ')');
			    t.prev().attr("src", "checked.png");
			}
			if (data.grantAdministratorApproved) {
				var t = $(':input[name=grantAdministratorApproved]');
				t.attr('checked', true).after('(' + data.grantAdministratorApproved.name + ')');
			    t.prev().attr("src", "checked.png");
			}
			if (data.commentToCurrent && stage !== 'completed') {
				$(':input[name=commentToCurrent]').val(data.commentToCurrent);
				$('.commentToCurrentArea').show();
			}
			if (stage === 'completed') {
				$('.applicantOnly,.supervisorOnly,.administratorOnly,textarea,select').attr('disabled', 'disabled').addClass('readonly');
				$(':input').attr('disabled', 'disabled');
            } else if (stage === 'supervisor') {
				$('.applicantOnly,.administratorOnly').attr('disabled', 'disabled').addClass('readonly');
				$('.supervisorHighlight').addClass('highlight');
			} else if (stage === 'grantholder') {
				$('.supervisorOnly,.applicantOnly').attr('disabled', 'disabled').addClass('readonly');
				$('.grantAdministratorHighlight').addClass('highlight');
			} else if (stage === 'supervisorgrantholder') {
				$('.applicantOnly').attr('disabled', 'disabled').addClass('readonly');
				$('.supervisorHighlight,.grantAdministratorHighlight').addClass('highlight');
			} else if (stage === 'applicant') {
				$('.supervisorOnly,.administratorOnly').attr('disabled', 'disabled').addClass('readonly');
				$('.supervisorGrantAdminOnly').hide();
				if (!data.supervisorApproved && !data.grantAdministratorApproved)
					$('.approvalArea').hide();
            }
			recalculateDaily();
			recalculateTotal();
            if (stage === 'completed') {
                $('#pdfLink').attr('href',"travel/application.pdf?application=" + $('#id').val());
                $('#pdf').show();
            } else {
                $('#pdf').hide();
            }
		});

		function dateString(timeMillis) {
			if (!timeMillis) return '';
			var date = new Date(timeMillis);
			return date.getDate() + '/' + (date.getMonth()+1) + '/' + date.getFullYear();
		}

		function dateMillis(dateString) {
			var values = dateString.split('/');
			var date = new Date();
			date.setDate(values[0]);
			date.setMonth(values[1]-1); //zero-indexed
			date.setFullYear(values[2]);
			return date.getTime();
		}

		// submit handler
		$('#send').click(function() {
			
			// input validation
			var m = [];
			var student = $(':input[name=status]:checked').val() != 'faculty';
			if (!$('input:radio[name=source]:checked').val())
				m.push('Funding source not specified!');
			if ($('input:radio[name=source]:checked').val() == 'other' && !$.trim($(':input[name=projectName]').val()))
				m.push('Funding source project name not specified!');
			if ($('input:radio[name=source]:checked').val() == 'other' && !$.trim($(':input[name=grantHolder]').val()))
				m.push('Grant administrator not specified!');
			if (!$('#researchGroup').val())
				m.push('Research group not specified!');
			if (student && !$('#supervisor').val())
				m.push('Supervisor not specified!');
			if (!$.trim($(':input[name=destinationCity]').val()))
				m.push('Destination city not specified!');
			if (!$.trim($(':input[name=destinationCountry]').val()))
				m.push('Destination country not specified!');
			if (!$.trim($(':input[name=travelStart]').val()) || !$.trim($(':input[name=travelEnd]').val()))
				m.push('Travel dates not specified!');
			else if (isNaN(dateMillis($('#travelStart').val())) || isNaN(dateMillis($('#travelEnd').val())))
				m.push('Invalid travel dates');
			if (!$.trim($('input:radio[name=purpose]:checked').val()))
				m.push('Purpose not specified!');
			if ($('input:radio[name=purpose]:checked').val() == 'guest' && !$.trim($(':input[name=guestName]').val()))
				m.push('Guest name not specified!');
			if ($('input:radio[name=purpose]:checked').val() == 'other' && !$.trim($(':input[name=otherPurpose]').val()))
				m.push('Purpose not specified!');
			if ($('#totalExpenses').val() == 0)
				m.push('Expenses missing!');
			if (!$.trim($(':input[name=purposeDetails]').val()))
				m.push('Detailed description missing!');
			if (!$.trim($('#commentsToReceiver').val()) &&
					((stage === 'supervisor' && !$('#supervisorApproved:checked').length) ||
					 (stage === 'grantholder' && !$('#grantAdministratorApproved:checked').length) ||
					 (stage === 'supervisorgrantholder' && 
							 (!$('#supervisorApproved:checked').length || !$('#grantAdministratorApproved:checked').length))))
				m.push("You have not approved the application, and there is no explanation under 'Comments if not approved'");
			if (m.length > 0) {
				alert('Some information is missing:\n\n' + m.join('\n'));
				return;
			}
			
			// send application
			var applicationToSave = {
					researchGroup: $('#researchGroup').val(),
					destinationCity: $('#destinationCity').val(),
					destinationCountry: $('#destinationCountry').val(),
					recommendationSupervisor : $('#recommendationSupervisor').val(),
					remarks: $(':input[name=remarks]').val(),
					supervisorApproved: !!$('#supervisorApproved:checked').length,
					grantAdministratorApproved: !!$('#grantAdministratorApproved:checked').length,
					commentToCurrent : $('#commentsToReceiver').val(), // receiver becomes current
			};
			
			var status = $(':input[name=status][checked=checked]');
			if (status.length)
				applicationToSave.status = status.attr('value');

			var source = $(':input[name=source][checked=checked]');
			if (source.length) {
				applicationToSave.source = {
					type: source.attr('value')
				};
				if (applicationToSave.source.type === 'other') {
					applicationToSave.source.projectName = $('#projectName').val();
					applicationToSave.source.grantHolder = $('#grantHolder').val();
				};
			}

			var supervisor = $('#supervisor').val();
			if (supervisor)
				applicationToSave.supervisor = {username: supervisor};
			var recommendationSupervisor = $('#recommendationSupervisor').val();
			if (recommendationSupervisor)
				applicationToSave.recommendationSupervisor = recommendationSupervisor;

			var travelStartMillis = dateMillis($('#travelStart').val());
			if (!isNaN(travelStartMillis))
				applicationToSave.travelStart = travelStartMillis;
			var travelEndMillis = dateMillis($('#travelEnd').val());
			if (!isNaN(travelEndMillis))
				applicationToSave.travelEnd = travelEndMillis;

			var days = parseInt($('#days').val());
			if (!isNaN(days))
				applicationToSave.days = days;

			var purpose = $(':input[name=purpose][checked=checked]');
			if (purpose.length) {
				applicationToSave.purpose = {
						type: purpose.attr('value'),
						description: $('#purposeDetails').val()
				};
				switch (applicationToSave.purpose.type) {
				case 'participation': 
					applicationToSave.purpose.presentation = !!$('#presenting:checked').length; 
					break;
				case 'guest': 
					applicationToSave.purpose.name = $('#guestName').val(); 
					break;
				case 'other': 
					applicationToSave.purpose.text = $('#otherPurpose').val();
					break;
				}
			}

			applicationToSave.expenses = {
					receiveDailyAllowance: !!$('#receiveDailyAllowance:checked').length,
					otherText: $('#otherExpensesDescription').val(),
			};

			var travelExpense = parseInt($('#travelExpenses').val());
			if (!isNaN(travelExpense))
				applicationToSave.expenses.travelExpense = travelExpense;

			var registrationExpense = parseInt($('#registrationFee').val());
			if (!isNaN(registrationExpense))
				applicationToSave.expenses.registrationFee = registrationExpense;

			var hotelExpense = parseInt($('#hotelExpenses').val());
			if (!isNaN(hotelExpense))
				applicationToSave.expenses.hotelExpense = hotelExpense;

			var otherExpense = parseInt($('#otherExpenses').val());
			if (!isNaN(otherExpense))
				applicationToSave.expenses.otherExpense = otherExpense;

            var data = {
                JSONApplication: JSON.stringify(applicationToSave)
            };
            var id = $('#id').val();
            if (id != '')
            	data.application = id; 
            $.ajax({
				type: 'POST',
				url: 'travel/storeApplication',
				data: data,
				success: function() {
					$('.caption,#application').hide();
					$('#thanks').fadeIn('slow');
				}
			});
		});
	}
});
