Ext.ux.FileUploader=function(a){Ext.apply(this,a);Ext.ux.FileUploader.superclass.constructor.apply(this,arguments);this.addEvents("beforeallstart","allfinished","beforefilestart","filefinished","progress")};Ext.extend(Ext.ux.FileUploader,Ext.util.Observable,{baseParams:{cmd:"upload",dir:"."},concurrent:true,enableProgress:true,jsonErrorText:"Cannot decode JSON object",maxFileSize:524288,progressIdName:"UPLOAD_IDENTIFIER",progressInterval:2000,progressUrl:"progress.php",progressMap:{bytes_total:"bytesTotal",bytes_uploaded:"bytesUploaded",est_sec:"estSec",files_uploaded:"filesUploaded",speed_average:"speedAverage",speed_last:"speedLast",time_last:"timeLast",time_start:"timeStart"},singleUpload:false,unknownErrorText:"Unknown error",upCount:0,createForm:function(a){var c=parseInt(Math.random()*10000000000,10);var b=Ext.getBody().createChild({tag:"form",action:this.url,method:"post",cls:"x-hidden",id:Ext.id(),cn:[{tag:"input",type:"hidden",name:"APC_UPLOAD_PROGRESS",value:c},{tag:"input",type:"hidden",name:this.progressIdName,value:c},{tag:"input",type:"hidden",name:"MAX_FILE_SIZE",value:this.maxFileSize}]});if(a){a.set("form",b);a.set("progressId",c)}else{this.progressId=c}return b},deleteForm:function(b,a){b.remove();if(a){a.set("form",null)}},fireFinishEvents:function(a){if(true!==this.eventsSuspended&&!this.singleUpload){this.fireEvent("filefinished",this,a&&a.record)}if(true!==this.eventsSuspended&&0===this.upCount){this.stopProgress();this.fireEvent("allfinished",this)}},getIframe:function(a){var b=null;var c=a.get("form");if(c&&c.dom&&c.dom.target){b=Ext.get(c.dom.target)}return b},getOptions:function(a,c){var b={url:this.url,method:"post",isUpload:true,scope:this,callback:this.uploadCallback,record:a,params:this.getParams(a,c)};return b},getParams:function(a,c){var b={path:this.path};Ext.apply(b,this.baseParams||{},c||{});return b},processSuccess:function(c,b,d){var a=false;if(this.singleUpload){this.store.each(function(e){e.set("state","done");e.set("error","");e.commit()})}else{a=c.record;a.set("state","done");a.set("error","");a.commit()}this.deleteForm(c.form,a)},processFailure:function(e,c,d){var a=e.record;var b;if(this.singleUpload){b=this.store.queryBy(function(f){var g=f.get("state");return"done"!==g&&"uploading"!==g});b.each(function(f){var g=d.errors?d.errors[f.id]:this.unknownErrorText;if(g){f.set("state","failed");f.set("error",g);Ext.getBody().appendChild(f.get("input"))}else{f.set("state","done");f.set("error","")}f.commit()},this);this.deleteForm(e.form)}else{if(d&&"object"===Ext.type(d)){a.set("error",d.errors&&d.errors[a.id]?d.errors[a.id]:this.unknownErrorText)}else{if(d){a.set("error",d)}else{if(c&&c.responseText){a.set("error",c.responseText)}else{a.set("error",this.unknownErrorText)}}}a.set("state","failed");a.commit()}},requestProgress:function(){var a,b;var c={url:this.progressUrl,method:"post",params:{},scope:this,callback:function(f,i,d){var h;if(true!==i){return}try{h=Ext.decode(d.responseText)}catch(g){return}if("object"!==Ext.type(h)||true!==h.success){return}if(this.singleUpload){this.progress={};for(b in h){if(this.progressMap[b]){this.progress[this.progressMap[b]]=parseInt(h[b],10)}}if(true!==this.eventsSuspended){this.fireEvent("progress",this,this.progress)}}else{for(b in h){if(this.progressMap[b]&&f.record){f.record.set(this.progressMap[b],parseInt(h[b],10))}}if(f.record){f.record.commit();if(true!==this.eventsSuspended){this.fireEvent("progress",this,f.record.data,f.record)}}}this.progressTask.delay(this.progressInterval)}};if(this.singleUpload){c.params[this.progressIdName]=this.progressId;c.params.APC_UPLOAD_PROGRESS=this.progressId;Ext.Ajax.request(c)}else{a=this.store.query("state","uploading");a.each(function(d){c.params[this.progressIdName]=d.get("progressId");c.params.APC_UPLOAD_PROGRESS=c.params[this.progressIdName];c.record=d;(function(){Ext.Ajax.request(c)}).defer(250)},this)}},setPath:function(a){this.path=a},setUrl:function(a){this.url=a},startProgress:function(){if(!this.progressTask){this.progressTask=new Ext.util.DelayedTask(this.requestProgress,this)}this.progressTask.delay.defer(this.progressInterval/2,this.progressTask,[this.progressInterval])},stopProgress:function(){if(this.progressTask){this.progressTask.cancel()}},stopAll:function(){var a=this.store.query("state","uploading");a.each(this.stopUpload,this)},stopUpload:function(a){var b=false;if(a){b=this.getIframe(a);this.stopIframe(b);this.upCount--;this.upCount=0>this.upCount?0:this.upCount;a.set("state","stopped");this.fireFinishEvents({record:a})}else{if(this.form){b=Ext.fly(this.form.dom.target);this.stopIframe(b);this.upCount=0;this.fireFinishEvents()}}},stopIframe:function(a){if(a){try{a.dom.contentWindow.stop();a.remove.defer(250,a)}catch(b){}}},upload:function(){var a=this.store.queryBy(function(b){return"done"!==b.get("state")});if(!a.getCount()){return}if(true!==this.eventsSuspended&&false===this.fireEvent("beforeallstart",this)){return}if(this.singleUpload){this.uploadSingle()}else{a.each(this.uploadFile,this)}if(true===this.enableProgress){this.startProgress()}},uploadCallback:function(b,f,a){var d;this.upCount--;this.form=false;if(true===f){try{d=Ext.decode(a.responseText)}catch(c){this.processFailure(b,a,this.jsonErrorText);this.fireFinishEvents(b);return}if(true===d.success){this.processSuccess(b,a,d)}else{this.processFailure(b,a,d)}}else{this.processFailure(b,a)}this.fireFinishEvents(b)},uploadFile:function(a,e){if(true!==this.eventsSuspended&&false===this.fireEvent("beforefilestart",this,a)){return}var c=this.createForm(a);var b=a.get("input");b.set({name:b.id});c.appendChild(b);var d=this.getOptions(a,e);d.form=c;a.set("state","uploading");a.set("pctComplete",0);this.upCount++;Ext.Ajax.request(d);this.getIframe.defer(100,this,[a])},uploadSingle:function(){var a=this.store.queryBy(function(d){return"done"!==d.get("state")});if(!a.getCount()){return}var b=this.createForm();a.each(function(d){var e=d.get("input");e.set({name:e.id});b.appendChild(e);d.set("state","uploading")},this);var c=this.getOptions();c.form=b;this.form=b;this.upCount++;Ext.Ajax.request(c)}});Ext.reg("fileuploader",Ext.ux.FileUploader);Ext.namespace("Ext.ux.form");Ext.ux.form.BrowseButton=Ext.extend(Ext.Button,{inputFileName:"file",debug:false,FLOAT_EL_WIDTH:60,FLOAT_EL_HEIGHT:18,buttonCt:null,clipEl:null,floatEl:null,inputFileEl:null,originalHandler:null,originalScope:null,initComponent:function(){Ext.ux.form.BrowseButton.superclass.initComponent.call(this);this.originalHandler=this.handler;this.originalScope=this.scope;this.handler=null;this.scope=null},onRender:function(d,b){Ext.ux.form.BrowseButton.superclass.onRender.call(this,d,b);this.buttonCt=this.el.child(".x-btn-center em");this.buttonCt.position("relative");var c={position:"absolute",overflow:"hidden",top:"0px",left:"0px"};if(Ext.isIE){Ext.apply(c,{left:"-3px",top:"-3px"})}else{if(Ext.isGecko){Ext.apply(c,{left:"-3px",top:"-3px"})}else{if(Ext.isSafari){Ext.apply(c,{left:"-4px",top:"-2px"})}}}this.clipEl=this.buttonCt.createChild({tag:"div",style:c});this.setClipSize();this.clipEl.on({mousemove:this.onButtonMouseMove,mouseover:this.onButtonMouseMove,scope:this});this.floatEl=this.clipEl.createChild({tag:"div",style:{position:"absolute",width:this.FLOAT_EL_WIDTH+"px",height:this.FLOAT_EL_HEIGHT+"px",overflow:"hidden"}});if(this.debug){this.clipEl.applyStyles({"background-color":"green"});this.floatEl.applyStyles({"background-color":"red"})}else{this.clipEl.setOpacity(0)}var a=this.el.child(this.buttonSelector);a.on("focus",this.onButtonFocus,this);if(Ext.isIE){this.el.on("keydown",this.onButtonKeyDown,this)}this.createInputFile()},setClipSize:function(){if(this.clipEl){var b=this.buttonCt.getWidth();var a=this.buttonCt.getHeight();if(b===0||a===0){this.setClipSize.defer(100,this)}else{if(Ext.isIE){b=b+5;a=a+5}else{if(Ext.isGecko){b=b+6;a=a+6}else{if(Ext.isSafari){b=b+6;a=a+6}}}this.clipEl.setSize(b,a)}}},createInputFile:function(){this.floatEl.select("em").each(function(a){a.remove()});this.inputFileEl=this.floatEl.createChild({tag:"input",type:"file",size:1,name:this.inputFileName||Ext.id(this.el),tabindex:this.tabIndex,style:{position:"absolute",cursor:"pointer",right:"0px",top:"0px"}});this.inputFileEl=this.inputFileEl.child("input")||this.inputFileEl;this.inputFileEl.on({click:this.onInputFileClick,change:this.onInputFileChange,focus:this.onInputFileFocus,select:this.onInputFileFocus,blur:this.onInputFileBlur,scope:this});if(this.tooltip){if(typeof this.tooltip=="object"){Ext.QuickTips.register(Ext.apply({target:this.inputFileEl},this.tooltip))}else{this.inputFileEl.dom[this.tooltipType]=this.tooltip}}},onButtonFocus:function(a){if(this.inputFileEl){this.inputFileEl.focus();a.stopEvent()}},onButtonKeyDown:function(a){if(this.inputFileEl&&a.getKey()==Ext.EventObject.SPACE){this.inputFileEl.dom.click();a.stopEvent()}},onButtonMouseMove:function(b){var a=b.getXY();a[0]-=this.FLOAT_EL_WIDTH/2;a[1]-=this.FLOAT_EL_HEIGHT/2;this.floatEl.setXY(a)},onInputFileFocus:function(a){if(!this.isDisabled){this.el.addClass("x-btn-over")}},onInputFileBlur:function(a){this.el.removeClass("x-btn-over")},onInputFileClick:function(a){a.stopPropagation()},onInputFileChange:function(){if(this.originalHandler){this.originalHandler.call(this.originalScope,this)}},detachInputFile:function(b){var a=this.inputFileEl;if(typeof this.tooltip=="object"){Ext.QuickTips.unregister(this.inputFileEl)}else{this.inputFileEl.dom[this.tooltipType]=null}this.inputFileEl.removeAllListeners();this.inputFileEl=null;if(!b){this.createInputFile()}return a},getInputFile:function(){return this.inputFileEl},disable:function(){Ext.ux.form.BrowseButton.superclass.disable.call(this);this.inputFileEl.dom.disabled=true},enable:function(){Ext.ux.form.BrowseButton.superclass.enable.call(this);this.inputFileEl.dom.disabled=false}});Ext.reg("browsebutton",Ext.ux.form.BrowseButton);Ext.ux.UploadPanel=Ext.extend(Ext.Panel,{addIconCls:"add",addText:"Add",bodyStyle:"padding:2px",buttonsAt:"tbar",clickRemoveText:"Click to remove",clickStopText:"Click to stop",emptyText:"No files",enableProgress:true,errorText:"Error",fileCls:"file",fileQueuedText:"File <b>{0}</b> is queued for upload",fileDoneText:"File <b>{0}</b> has been successfully uploaded",fileFailedText:"File <b>{0}</b> failed to upload",fileStoppedText:"File <b>{0}</b> stopped by user",fileUploadingText:"Uploading file <b>{0}</b>",maxFileSize:524288,maxLength:18,removeAllIconCls:"icon-cross",removeAllText:"Remove All",removeIconCls:"icon-minus",removeText:"Remove",selectedClass:"ux-up-item-selected",singleUpload:false,stopAllText:"Stop All",stopIconCls:"icon-stop",uploadText:"Upload",uploadIconCls:"icon-upload",workingIconCls:"icon-working",initComponent:function(){var d={xtype:"browsebutton",text:this.addText+"...",iconCls:this.addIconCls,scope:this,handler:this.onAddFile};var b={xtype:"button",iconCls:this.uploadIconCls,text:this.uploadText,scope:this,handler:this.onUpload,disabled:true};var e={xtype:"button",iconCls:this.removeAllIconCls,tooltip:this.removeAllText,scope:this,handler:this.onRemoveAllClick,disabled:true};if("body"!==this.buttonsAt){this[this.buttonsAt]=[d,b,"->",e]}var a=[{name:"id",type:"text",system:true},{name:"shortName",type:"text",system:true},{name:"fileName",type:"text",system:true},{name:"filePath",type:"text",system:true},{name:"fileCls",type:"text",system:true},{name:"input",system:true},{name:"form",system:true},{name:"state",type:"text",system:true},{name:"error",type:"text",system:true},{name:"progressId",type:"int",system:true},{name:"bytesTotal",type:"int",system:true},{name:"bytesUploaded",type:"int",system:true},{name:"estSec",type:"int",system:true},{name:"filesUploaded",type:"int",system:true},{name:"speedAverage",type:"int",system:true},{name:"speedLast",type:"int",system:true},{name:"timeLast",type:"int",system:true},{name:"timeStart",type:"int",system:true},{name:"pctComplete",type:"int",system:true}];if(Ext.isArray(this.customFields)){a.push(this.customFields)}this.store=new Ext.data.SimpleStore({id:0,fields:a,data:[]});Ext.apply(this,{items:[{xtype:"dataview",itemSelector:"div.ux-up-item",store:this.store,selectedClass:this.selectedClass,singleSelect:true,emptyText:this.emptyText,tpl:this.tpl||new Ext.XTemplate('<tpl for="."><div class="ux-up-item"><div class="ux-up-icon-file {fileCls}">&#160;</div><div class="ux-up-text x-unselectable" qtip="{fileName}">{shortName}</div><div id="remove-{[values.input.id]}" class="ux-up-icon-state ux-up-icon-{state}"qtip="{[this.scope.getQtip(values)]}">&#160;</div></div></tpl>',{scope:this}),listeners:{click:{scope:this,fn:this.onViewClick}}}]});Ext.ux.UploadPanel.superclass.initComponent.apply(this,arguments);this.view=this.items.itemAt(0);this.addEvents("beforefileadd","fileadd","beforefileremove","fileremove","beforequeueclear","queueclear","beforeupload","allfinished");this.relayEvents(this.view,["beforeclick","beforeselect","click","containerclick","contextmenu","dblclick","selectionchange"]);var c={store:this.store,singleUpload:this.singleUpload,maxFileSize:this.maxFileSize,enableProgress:this.enableProgress,url:this.url,path:this.path};if(this.baseParams){c.baseParams=this.baseParams}this.uploader=new Ext.ux.FileUploader(c);this.relayEvents(this.uploader,["beforeallstart","allfinished","progress"]);this.on({beforeallstart:{scope:this,fn:function(){this.uploading=true;this.updateButtons()}},allfinished:{scope:this,fn:function(){this.uploading=false;this.updateButtons()}},progress:{fn:this.onProgress.createDelegate(this)}})},onRender:function(){Ext.ux.UploadPanel.superclass.onRender.apply(this,arguments);var a="tbar"===this.buttonsAt?this.getTopToolbar():this.getBottomToolbar();this.addBtn=Ext.getCmp(a.items.first().id);this.uploadBtn=Ext.getCmp(a.items.itemAt(1).id);this.removeAllBtn=Ext.getCmp(a.items.last().id)},getQtip:function(a){var b="";switch(a.state){case"queued":b=String.format(this.fileQueuedText,a.fileName);b+="<br>"+this.clickRemoveText;break;case"uploading":b=String.format(this.fileUploadingText,a.fileName);b+="<br>"+a.pctComplete+"% done";b+="<br>"+this.clickStopText;break;case"done":b=String.format(this.fileDoneText,a.fileName);b+="<br>"+this.clickRemoveText;break;case"failed":b=String.format(this.fileFailedText,a.fileName);b+="<br>"+this.errorText+":"+a.error;b+="<br>"+this.clickRemoveText;break;case"stopped":b=String.format(this.fileStoppedText,a.fileName);b+="<br>"+this.clickRemoveText;break}return b},getFileName:function(a){return a.getValue().split(/[\/\\]/).pop()},getFilePath:function(a){return a.getValue().replace(/[^\/\\]+$/,"")},getFileCls:function(a){var b=a.split(".");if(1===b.length){return this.fileCls}else{return this.fileCls+"-"+b.pop().toLowerCase()}},onAddFile:function(c){if(true!==this.eventsSuspended&&false===this.fireEvent("beforefileadd",this,c.getInputFile())){return}var a=c.detachInputFile();a.addClass("x-hidden");var d=this.getFileName(a);var b=new this.store.recordType({input:a,fileName:d,filePath:this.getFilePath(a),shortName:Ext.util.Format.ellipsis(d,this.maxLength),fileCls:this.getFileCls(d),state:"queued"},a.id);b.commit();this.store.add(b);this.syncShadow();this.uploadBtn.enable();this.removeAllBtn.enable();if(true!==this.eventsSuspended){this.fireEvent("fileadd",this,this.store,b)}this.doLayout()},onDestroy:function(){if(this.uploader){this.uploader.stopAll();this.uploader.purgeListeners();this.uploader=null}if(this.view){this.view.purgeListeners();this.view.destroy();this.view=null}if(this.store){this.store.purgeListeners();this.store.destroy();this.store=null}},onProgress:function(h,f,g){var e,d,i,a,j,k,b,c;if(g){a=g.get("state");e=g.get("bytesTotal")||1;d=g.get("bytesUploaded")||0;if("uploading"===a){i=Math.round(1000*d/e)/10}else{if("done"===a){i=100}else{i=0}}g.set("pctComplete",i);j=this.store.indexOf(g);k=Ext.get(this.view.getNode(j));if(k){b=k.getWidth();k.applyStyles({"background-position":b*i/100+"px"})}}},onRemoveFile:function(a){if(true!==this.eventsSuspended&&false===this.fireEvent("beforefileremove",this,this.store,a)){return}var d=a.get("input");var b=d.up("em");d.remove();if(b){b.remove()}this.store.remove(a);var c=this.store.getCount();this.uploadBtn.setDisabled(!c);this.removeAllBtn.setDisabled(!c);if(true!==this.eventsSuspended){this.fireEvent("fileremove",this,this.store);this.syncShadow()}},onRemoveAllClick:function(a){if(true===this.uploading){this.stopAll()}else{this.removeAll()}},stopAll:function(){this.uploader.stopAll()},onViewClick:function(a,b,d,f){var c=f.getTarget("div:any(.ux-up-icon-queued|.ux-up-icon-failed|.ux-up-icon-done|.ux-up-icon-stopped)");if(c){this.onRemoveFile(this.store.getAt(b))}c=f.getTarget("div.ux-up-icon-uploading");if(c){this.uploader.stopUpload(this.store.getAt(b))}},onUpload:function(){if(true!==this.eventsSuspended&&false===this.fireEvent("beforeupload",this)){return false}this.uploader.upload()},setUrl:function(a){this.url=a;this.uploader.setUrl(a)},setPath:function(a){this.uploader.setPath(a)},updateButtons:function(){if(true===this.uploading){this.addBtn.disable();this.uploadBtn.disable();this.removeAllBtn.setIconClass(this.stopIconCls);this.removeAllBtn.getEl().child(this.removeAllBtn.buttonSelector).dom[this.removeAllBtn.tooltipType]=this.stopAllText}else{this.addBtn.enable();this.uploadBtn.enable();this.removeAllBtn.setIconClass(this.removeAllIconCls);this.removeAllBtn.getEl().child(this.removeAllBtn.buttonSelector).dom[this.removeAllBtn.tooltipType]=this.removeAllText}},removeAll:function(){var a=this.eventsSuspended;if(false!==this.eventsSuspended&&false===this.fireEvent("beforequeueclear",this,this.store)){return false}this.suspendEvents();this.store.each(this.onRemoveFile,this);this.eventsSuspended=a;if(true!==this.eventsSuspended){this.fireEvent("queueclear",this,this.store)}this.syncShadow()},syncShadow:function(){if(this.contextmenu&&this.contextmenu.shadow){this.contextmenu.getEl().shadow.show(this.contextmenu.getEl())}}});Ext.reg("uploadpanel",Ext.ux.UploadPanel);Ext.namespace("Toc.products");
Toc.products.ProductsGrid = function(config) {

  config = config || {};
  
  config.border = false;
  config.region = 'center';
  config.viewConfig = {emptyText: TocLanguage.gridNoRecords};
  config.animCollapse = false;
  config.enableDragDrop = true;
  config.ddGroup = 'productDD';

  config.ds = new Ext.data.Store({
    url: Toc.CONF.CONN_URL,
    baseParams: {
      module: 'products',
      action: 'list_products'        
    },
    reader: new Ext.data.JsonReader({
      root: Toc.CONF.JSON_READER_ROOT,
      totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
      id: 'products_id'
    }, [
      {name: 'products_id'},
      {name: 'products_name'},
      {name: 'products_frontpage'},
      {name: 'products_status'},
      {name: 'products_price', type: 'string'},
      {name: 'products_quantity', type: 'int'}
    ]),
    remoteSort: true
  });
  
  renderStatus = function(status) {
    if(status == 1) {
      return '<img class="img-button" src="images/icon_status_green.gif" />&nbsp;<img class="img-button btn-status-off" style="cursor: pointer" src="images/icon_status_red_light.gif" />';
    }else {
      return '<img class="img-button btn-status-on" style="cursor: pointer" src="images/icon_status_green_light.gif" />&nbsp;<img class="img-button" src= "images/icon_status_red.gif" />';
    }
  }; 
  
  config.rowActions = new Ext.ux.grid.RowActions({
    actions:[
      {iconCls: 'icon-edit-record', qtip: TocLanguage.tipEdit},
      {iconCls: 'icon-delete-record', qtip: TocLanguage.tipDelete},
      {iconCls: 'icon-copy-record', qtip: 'Duplicate Product'}],
      widthIntercept: Ext.isSafari ? 4 : 2
  });
  config.rowActions.on('action', this.onRowAction, this);    
  config.plugins = config.rowActions;
  
  config.sm = new Ext.grid.CheckboxSelectionModel();
  config.cm = new Ext.grid.ColumnModel([
    config.sm,
    {id:'products_name', header: "Products", sortable: true, dataIndex: 'products_name'},
    {header: "Front Page", align: 'center', renderer: renderStatus, dataIndex: 'products_frontpage', width: 90},
    {header: "Status", align: 'center', renderer: renderStatus, sortable: true, dataIndex: 'products_status', width: 80},
    {header: "Price", dataIndex: 'products_price', sortable: true, width: 80, align: 'right'},
    {header: "Quantity", dataIndex: 'products_quantity', sortable: true, width: 80, align: 'right'},
    config.rowActions
  ]);
  config.autoExpandColumn = 'products_name';
  
  config.txtSearch = new Ext.form.TextField({
    width:160,
    paramName: 'search'
  });
  
  config.tbar = [
    {
      text: TocLanguage.btnAdd,
      iconCls:'add',
      handler: this.onAdd,
      scope: this
    }, 
    '-', 
    {
      text: TocLanguage.btnDelete,
      iconCls:'remove',
      handler: this.onBatchDelete,
      scope: this
    }, 
    '-',
    { 
      text: TocLanguage.btnRefresh,
      iconCls:'refresh',
      handler: this.onRefresh,
      scope: this
    }, 
    '->',
    config.txtSearch,
    ' ', 
    {
      iconCls : 'search',
      handler : this.onSearch,
      scope : this
    }
  ];

  var thisObj = this;
  config.bbar = new Ext.PageToolbar({
    pageSize: Toc.CONF.GRID_PAGE_SIZE,
    store: config.ds,
    steps: Toc.CONF.GRID_STEPS,
    btnsConfig:[
      {
        text: TocLanguage.btnActivate,
        iconCls:'publish',
        handler: function(){
          thisObj.onBatchStatusClick(1);
        }
      },
      {
        text: TocLanguage.btnDeactivate,
        iconCls:'unpublish',
        handler: function(){
          thisObj.onBatchStatusClick(0);
        }        
      }
    ],
    beforePageText : TocLanguage.beforePageText,
    firstText: TocLanguage.firstText,
    lastText: TocLanguage.lastText,
    nextText: TocLanguage.nextText,
    prevText: TocLanguage.prevText,
    afterPageText: TocLanguage.afterPageText,
    refreshText: TocLanguage.refreshText,
    displayInfo: true,
    displayMsg: TocLanguage.displayMsg,
    emptyMsg: TocLanguage.emptyMsg,
    prevStepText: TocLanguage.prevStepText,
    nextStepText: TocLanguage.nextStepText
  });

  Toc.products.ProductsGrid.superclass.constructor.call(this, config);
};


Ext.extend(Toc.products.ProductsGrid, Ext.grid.GridPanel, {

  onAdd: function(){
    var dlg = this.owner.createProductDialog();

    dlg.on('saveSuccess', function(result){
      this.onRefresh();
      
      this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result});
    }, this);
    
    dlg.show(this.mainPanel.getCategoriesTree().getCategoriesPath(null));
  },
  
  onEdit: function(record) {
    var dlg = this.owner.createProductDialog(record.get("products_id"));
    dlg.setTitle(record.get("products_name"));
    
    dlg.on('saveSuccess', function(result) {
      this.onRefresh();
      
      this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result});
    }, this);
    
    dlg.show();
  },
  
  onDelete: function(record) {
    var productsId = record.get('products_id');
    
    Ext.MessageBox.confirm(
      TocLanguage.msgWarningTitle, 
      TocLanguage.msgDeleteConfirm,
      function(btn) {
        if (btn == 'yes') {
          Ext.Ajax.request({
            url: Toc.CONF.CONN_URL,
            params: {
              module: 'products',
              action: 'delete_product',
              products_id: productsId
            },
            callback: function(options, success, response){
              var result = Ext.decode(response.responseText);
              
              if (result.success == true) {
                this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result.feedback});
                this.getStore().reload();
              } else {
                Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
              }
            },
            scope: this
          });   
        }
      }, this);
  },
  
  onDuplicate: function(record) {
    var dlg = this.owner.createProductDuplicateDialog(record.get("products_id"));
    dlg.setTitle(record.get("products_name"));
    
    dlg.on('saveSuccess', function() {
      this.onRefresh();
    }, this);
    
    dlg.show();
  },
  
  onBatchDelete: function() {
    var keys = this.getSelectionModel().selections.keys;
    
    if (keys.length > 0) {
      var batch = keys.join(',');
      
      Ext.MessageBox.confirm(
        TocLanguage.msgWarningTitle, 
        TocLanguage.msgDeleteConfirm,
        function(btn) {
          if (btn == 'yes') {
            Ext.Ajax.request({
              url: Toc.CONF.CONN_URL,
              params: {
                module: 'products',
                action: 'delete_products',
                batch: batch
              },
              callback: function(options, success, response){
                var result = Ext.decode(response.responseText);
                
                if(result.success == true){
                  this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result.feedback});
                  this.getStore().reload();
                }else{
                  Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
                }
              },
              scope: this
            });   
          }
        }, 
        this);

    }else{
       Ext.MessageBox.alert(TocLanguage.msgInfoTitle, TocLanguage.msgMustSelectOne);
    }
  },
  
  onRefresh: function(){
    this.getStore().reload();
  },
  
  onClick: function(e, target) {
    var t = e.getTarget(),
        v = this.view,
        row = v.findRowIndex(t),
        col = v.findCellIndex(t),
        action = false,
        module;
        
    if (row !== false) {
      var btn = e.getTarget(".img-button");
      
      if (btn) {
        action = btn.className.replace(/img-button btn-/, '').trim();
      }

      if (action != 'img-button') {
        var productsId = this.getStore().getAt(row).get('products_id');
        var colname = this.getColumnModel().getDataIndex(col);
        
        if(colname == 'products_frontpage') {
          module = 'set_frontpage';
        }
        
        if(colname == 'products_status') {
          module = 'set_status';
        }

        switch(action) {
          case 'status-off':
          case 'status-on':
            flag = (action == 'status-on') ? 1 : 0;
            this.onAction(module, productsId, flag);
            break;
        }
      }
    }
  },
  
  onAction: function(action, productsId, flag) {
    Ext.Ajax.request({
      url: Toc.CONF.CONN_URL,
      params: {
        module: 'products',
        action: action,
        products_id: productsId,
        flag: flag
      },
      callback: function(options, success, response) {
        var result = Ext.decode(response.responseText);
        
        if (result.success == true) {
          var store = this.getStore();
          if(action == 'set_frontpage') {
            store.getById(productsId).set('products_frontpage', flag);
          } else {
            store.getById(productsId).set('products_status', flag);
          }
          store.commitChanges();
          
          this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result.feedback});
        } else {
          this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result.feedback});
        }
      },
      scope: this
    });
  },
  
  onRowAction:function(grid, record, action, row, col) {
    switch(action) {
      case 'icon-delete-record':
        this.onDelete(record);
        break;
      
      case 'icon-edit-record':
        this.onEdit(record);
        break;
      case 'icon-copy-record':
        this.onDuplicate(record);
        break;
    }
  },
  
  refreshGrid: function (categoriesId) {
    var store = this.getStore();

    store.baseParams['categories_id'] = categoriesId;
    store.load();
  },
  
  onSearch: function(){
    var filter = this.txtSearch.getValue() || null;
    var store = this.getStore();
          
    store.baseParams['search'] = filter;
    store.reload();
  },
  
  onBatchStatusClick: function(flag) {
    var keys = this.getSelectionModel().selections.keys;
    
    if(keys.length > 0) {
      var batch = keys.join(',');
      
      Ext.MessageBox.confirm(
        TocLanguage.msgWarningTitle, 
        flag ? TocLanguage.msgActiveConfirm : TocLanguage.msgDeactiveConfirm,
        function(btn) {
          if (btn == 'yes') {
            Ext.Ajax.request({
              url: Toc.CONF.CONN_URL,
              params: {
                module: 'products',
                action: 'batch_set_status',
                batch: batch,
                status: flag
              },
              callback: function(options, success, response){
                var result = Ext.decode(response.responseText);
                
                if(result.success == true){
                  this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result.feedback});

                  var store = this.getStore();
                  Ext.each(keys, function(key) {
                    store.getById(key).set('products_status', flag);
                  }, this);
                  
                  store.commitChanges();
                }else{
                  Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
                }
              },
              scope: this
            });   
          }
        }, 
        this);
    } else {
      Ext.MessageBox.alert(TocLanguage.msgInfoTitle, TocLanguage.msgMustSelectOne);
    }
  }
});
Toc.products.GeneralPanel = function(config) {
  config = config || {};
  
  config.title = 'General';
  config.activeTab = 0;
  config.deferredRender = false;
  config.items = this.buildForm();
  
  Toc.products.GeneralPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.GeneralPanel, Ext.TabPanel, {
  buildForm: function() {
    var panels = [];

    var langen_US = new Ext.Panel({
          title:'English',
          iconCls: 'icon-us-win',
          layout: 'form',
          labelSeparator: ' ',
          style: 'padding: 8px',
          defaults: {
            anchor: '98%'
          },
          items: [
            {xtype: 'textfield', fieldLabel: 'Name:', name: 'products_name[1]', allowBlank: false},
            {xtype: 'textfield', fieldLabel: 'Tags:', name: 'products_tags[1]'},
            {xtype: 'textarea', fieldLabel: 'Short Description:', name: 'products_short_description[1]', height: '50'},
            {xtype: 'htmleditor', fieldLabel: 'Description:', name: 'products_description[1]', height: 230},  
            {xtype: 'textfield', fieldLabel: 'URL:', name: 'products_url[1]'}
          ]
        });
        
        panels.push(langen_US);
            
    return panels;
  }
});
Toc.products.MetaPanel = function(config) {
  config = config || {};
  
  config.title = 'Meta Info';
  config.activeTab = 0;
  config.deferredRender = false;
  config.items = this.buildForm();
  
  Toc.products.MetaPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.MetaPanel, Ext.TabPanel, {
  buildForm: function() {
    var panels = [];
    this.txtProductUrl = [];
    
    var langen_US = new Ext.Panel({
          title:'English',
          iconCls: 'icon-us-win',
          layout: 'form',
          labelSeparator: ' ',
          style: 'padding: 8px',
          defaults: {
            anchor: '98%'
          },
          items: [
            {xtype: 'textfield', fieldLabel: 'Page Title:', name: 'products_page_title[1]'},
            {xtype: 'textfield', fieldLabel: 'Meta Keywords:', name: 'products_meta_keywords[1]'},
            {xtype: 'textarea', fieldLabel: 'Meta Description:', name: 'products_meta_description[1]', height: 200},
            this.txtProductUrl[1] = new Ext.form.TextField({fieldLabel: 'Friendly URL:', name: 'products_friendly_url[1]'})
          ]
        });
        
        panels.push(langen_US);
            
    return panels;
  }
});Toc.products.DataPanel = function(config) {
  config = config || {};
  
  config.title = 'Data';
  config.activeTab = 0;
  config.productsType = 1;
  config.tabExtraOptions = null;
  
  config.items = this.buildForm();
  
  Toc.products.DataPanel.superclass.constructor.call(this, config);
  
  this.addEvents({'producttypechange': true});
};

Ext.extend(Toc.products.DataPanel, Ext.TabPanel, {

  buildForm: function() {
    var dsProductsType = new Ext.data.SimpleStore({
      fields: ['id', 'text'],
      data: 
        [
          ['0','Simple Product'],
          ['1','Virtual Product'],
          ['2','Downloadable Product'],
          ['3','Gift Certificate']
        ]
    });

    this.cboProductsType = new Ext.form.ComboBox({
      fieldLabel: 'Product Type:',
      xtype: 'combo', 
      store: dsProductsType, 
      name: 'products_type_ids', 
      mode: 'local',
      hiddenName: 'products_type', 
      displayField: 'text', 
      valueField: 'id', 
      triggerAction: 'all', 
      editable: false,
      forceSelection: true,      
      value: '0',
      listeners: {
        select: this.onProductsTypeSelect,
        scope: this
      }
    });
    
    dsManufacturers = new Ext.data.Store({
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_manufacturers'
      },
      reader: new Ext.data.JsonReader({
        fields: ['id', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      autoLoad: true,
      listeners: {
        load: function() {this.cboManufacturers.setValue('0');},
        scope: this
      }
    });
    
    this.cboManufacturers = new Ext.form.ComboBox({
      fieldLabel: 'Manufacturer:', 
      xtype:'combo', 
      store: dsManufacturers, 
      name: 'manufacturers', 
      hiddenName: 'manufacturers_id', 
      displayField: 'text', 
      valueField: 'id', 
      triggerAction: 'all', 
      editable: false,
      forceSelection: true      
    });    
    
    dsWeightClasses = new Ext.data.Store({
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_weight_classes'
      },
      reader: new Ext.data.JsonReader({
          fields: ['id', 'text'],
          root: Toc.CONF.JSON_READER_ROOT
      }),
      autoLoad: true,
      listeners: {
        load: function() {this.cboWeightClasses.setValue('2');},
        scope: this
      }
    });
    
    this.cboWeightClasses = new Ext.form.ComboBox({
      width: 95, 
      xtype: 'combo', 
      store: dsWeightClasses, 
      id: 'combWeightClasses', 
      name: 'products_weight_class_ids', 
      hiddenName: 'products_weight_class', 
      hideLabel: true,
      displayField: 'text', 
      valueField: 'id', 
      triggerAction: 'all', 
      editable: false,
      forceSelection: true     
    });

      
    this.fsStatus = new Ext.form.FieldSet({
      title: 'Data', 
      layout: 'column', 
      width: 750,
      autoHeight: true,
      labelSeparator: ' ',
      items:[
        {
          columnWidth: .52,
          layout: 'form',
          labelSeparator: ' ',
          border: false,
          defaults: {
            anchor: '90%'
          },
          items:[
            this.cboProductsType,
            {
              layout: 'column',
              border: false,
              items:[
                {
                  width: 210,
                  layout: 'form',
                  labelSeparator: ' ',
                  border: false,
                  items:[
                    {fieldLabel: 'Status:', xtype:'radio', name: 'products_status', boxLabel: 'Enabled', xtype:'radio', inputValue: '1', checked: true}
                  ]
                },
                {
                  width: 80,
                  layout: 'form',
                  border: false,
                  items: [
                    {fieldLabel: 'Disabled', boxLabel: 'Disabled', xtype:'radio', name: 'products_status', hideLabel: true, inputValue: '0'}
                  ]
                }
              ]
            },
            {fieldLabel: 'Date Available:', name: 'products_date_available', format: 'Y-m-d', xtype: 'datefield', readOnly: true, width: 165}         
          ]
        },
        {
          columnWidth: .47,
          layout: 'form',
          labelSeparator: ' ',
          border: false,
          defaults: {
            anchor: '97%'
          },              
          items: [
            {fieldLabel: 'SKU:', xtype:'textfield', name: 'products_sku'},
            {fieldLabel: 'Model:', xtype:'textfield', name: 'products_model'},
            this.cboManufacturers,
            {
              layout: 'column',
              border: false,
              items:[
                {
                  width: 210,
                  layout: 'form',
                  labelSeparator: ' ',
                  border: false,
                  items:[
                    {fieldLabel: 'Weight:', xtype:'textfield', name: 'products_weight', width: 75}
                  ]
                },
                {
                  layout: 'form',
                  border: false,
                  items: this.cboWeightClasses
                }
              ]
            }
          ]
        }
      ]
    });  
      
    dsTaxClasses = new Ext.data.Store({
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_tax_classes'
      },
      reader: new Ext.data.JsonReader({
        fields: ['id', 'rate', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      autoLoad: true,
      listeners: {
        load: function() {this.cboTaxClass.setValue('0');},
        scope: this
      }
    });

    this.cboTaxClass = new Ext.form.ComboBox({
      fieldLabel: 'Tax Class:', 
      xtype:'combo', 
      store: dsTaxClasses, 
      name: 'products_tax_class', 
      hiddenName: 'products_tax_class_id', 
      displayField: 'text', 
      valueField: 'id', 
      triggerAction: 'all', 
      forceSelection: true,
      editable: false,
      forceSelection: true,
      listeners: {
        select: this.onTaxClassSelect,
        scope: this
      }
    });    
    
    this.txtPriceNet = new Ext.form.TextField({
      fieldLabel: 'Net Price:', 
      xtype:'textfield', 
      name: 'products_price',
      value: '0',
      listeners: {
        change: this.onPriceNetChange,
        scope: this
      }
    });
    
    this.txtPriceGross = new Ext.form.TextField({
      fieldLabel: 'Gross Price:', 
      xtype:'textfield', 
      name: 'products_price_gross',
      value: '0',
      listeners: {
        change: this.onPriceGrossChange,
        scope: this
      }
    });

    dsQuantityDiscountGroup = new Ext.data.Store({
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_quantity_discount_groups'
      },
      reader: new Ext.data.JsonReader({
        fields: ['id', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      autoLoad: true,
      listeners: {
        load: function() {this.cboPriceDiscountGroups.setValue('0');},
        scope: this
      }
    });

    this.cboPriceDiscountGroups = new Ext.form.ComboBox({
      fieldLabel: 'Price Discount Group:', 
      store: dsQuantityDiscountGroup, 
      name: 'quantity_discount_groups', 
      hiddenName: 'quantity_discount_groups_id', 
      displayField: 'text', 
      valueField: 'id', 
      triggerAction: 'all', 
      editable: false,
      forceSelection: true           
    });
                  
    this.fsPrice = new Ext.form.FieldSet({
      title: 'Price', 
      layout: 'form', 
      columnWidth: 0.49,
      height: 205,
      labelSeparator: ' ',
      defaults: {
        anchor: '95%'
      },
      items:[this.cboTaxClass, this.txtPriceNet, this.txtPriceGross, this.cboPriceDiscountGroups] 
    });

    dsUnitClass = new Ext.data.Store({
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_quantity_units'
      },
      reader: new Ext.data.JsonReader({
        fields: ['id', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      autoLoad: true,
      listeners: {
        load: function() {this.cboUnitClasses.setValue('1');},
        scope: this
      }
    });

    this.cboUnitClasses = new Ext.form.ComboBox({
      fieldLabel: 'Quantity Unit:', 
      store: dsUnitClass, 
      name: 'quantity_unit', 
      hiddenName: 'quantity_unit_class', 
      displayField: 'text', 
      valueField: 'id', 
      triggerAction: 'all', 
      editable: false,
      forceSelection: true     
    });
      
    this.fsInformation = new Ext.form.FieldSet({
      title: 'Information', 
      layout: 'form', 
      height: 205,
      labelSeparator: ' ',
      columnWidth: 0.51,
      style: 'margin-left: 10px',
      defaults: {
        anchor: '95%'
      },
      items:[
        this.txtQuantity = new Ext.form.NumberField({fieldLabel: 'Quantity:', name: 'products_quantity', allowDecimals: false, value: 0}) , 
        {fieldLabel: 'Min. Order Quantity:', xtype:'numberfield', name: 'products_moq', allowDecimals: false, value: 1},
        {fieldLabel: 'Quantity Increment:', xtype:'numberfield', name: 'order_increment', allowDecimals: false, value: 1},
        this.cboUnitClasses,
        this.txtMaxOrderQuantity = new Ext.form.NumberField({fieldLabel: 'Max. Order Quantity:', name: 'products_max_order_quantity', allowDecimals: false, disabled:true, minValue: 1}),
        this.chkUnlimited = new Ext.form.Checkbox({
          fieldLabel: '',
          boxLabel: 'Unlimited',
          name: 'unlimited',
          checked: true,
          listeners: {
            check: this.onChkUnlimitedChecked,
            scope: this
          }
        })
       ] 
    });
    
    var pnlGeneral = new Ext.Panel({
      title: 'General',
      style: 'padding: 10px',
      items: [
        this.fsStatus,
        {
          layout: 'column',
          border: false,
          width: 750,
          items: [
            this.fsPrice,
            this.fsInformation
          ]
        }
      ]
    });  
    
    return pnlGeneral;      
  },
  
  getTaxRate: function() {
    rate = 0;
    rateId = this.cboTaxClass.getValue();
    store = this.cboTaxClass.getStore();

    for (i = 0; i < store.getCount(); i++) {
      record = store.getAt(i);
       
      if(record.get('id') == rateId) {
        rate = record.get('rate');
        break;
      }
    }
    
    return rate;  
  },
  
  onPriceNetChange: function() {
    value = this.txtPriceNet.getValue();
    rate = this.getTaxRate();

    if (rate > 0) {
      value = value * ((rate / 100) + 1);
    }

    this.txtPriceGross.setValue(Math.round(value * Math.pow(10, 4)) / Math.pow(10, 4));
  },
  
  onPriceGrossChange: function() {
    value = this.txtPriceGross.getValue();
    rate = this.getTaxRate();

    if (rate > 0) {
      value = value / ((rate / 100) + 1);
    }

    this.txtPriceNet.setValue(Math.round(value * Math.pow(10, 4)) / Math.pow(10, 4));
  },
  
  onTaxClassSelect: function(combo, record) {
    value = this.txtPriceNet.getValue();
    rate = record.get('rate');
    
    if (rate > 0) {
      value = value * ((rate / 100) + 1);
    }
    
    this.txtPriceGross.setValue(Math.round(value * Math.pow(10, 4)) / Math.pow(10, 4));
  },
  
  onProductsTypeSelect: function(combo, record) {
    var type = record.get('id');
    
    if (this.productsType != type) {
      if ( (this.productsType != '0') && (this.productsType != '1') ) {
        this.remove(this.tabExtraOptions);
      }
      
      this.productsType = type;
      if(this.productsType == '2') {
        this.tabExtraOptions = new Toc.products.DownloadablesPanel();
        this.add(this.tabExtraOptions);
        this.setActiveTab(this.tabExtraOptions);
      } else if (this.productsType == '3') {
        this.tabExtraOptions = new Toc.products.GiftCertificatesPanel({owner: this});
        this.add(this.tabExtraOptions);
        this.setActiveTab(this.tabExtraOptions);   
      }
      
      //tax class
      this.updateCboTaxClass(type);
      
      this.fireEvent('producttypechange', type);
    }
  },  
  
  updateCboTaxClass: function (type) {
    if (type == '3') {
      this.cboTaxClass.setValue('0');
      this.cboTaxClass.disable();
    } else {
      this.cboTaxClass.enable();
    }
  },

  onVariantsChange: function(hasVariant, quantity) {
    if(hasVariant) {
      this.txtQuantity.disable();
      this.txtQuantity.setValue(quantity);
    } else {
      this.txtQuantity.enable();
    }
  },
  
  onChkUnlimitedChecked: function(checkbox, checked) {
    if (checked) {
      this.txtMaxOrderQuantity.disable();
      this.txtMaxOrderQuantity.allowBlank = true;
      this.txtMaxOrderQuantity.setValue('');
    } else {
      this.txtMaxOrderQuantity.enable();
      this.txtMaxOrderQuantity.allowBlank = false;
    }
  },
  
  loadExtraOptionTab: function(data) {
    var type = data.products_type;
    
    if (type == '2') {
      this.tabExtraOptions = new Toc.products.DownloadablesPanel();
      this.add(this.tabExtraOptions);
      this.setActiveTab(this.tabExtraOptions);
      this.setActiveTab(0);
      this.tabExtraOptions.loadForm(data);
    } else if (type == '3') {
      this.tabExtraOptions = new Toc.products.GiftCertificatesPanel({owner: this});
      this.add(this.tabExtraOptions);
      this.setActiveTab(this.tabExtraOptions);
      this.setActiveTab(0);
      this.tabExtraOptions.loadForm(data);
    }
    
    if (data.products_max_order_quantity > 0) {
      this.txtMaxOrderQuantity.enable();
      this.txtMaxOrderQuantity.setValue(data.products_max_order_quantity);
      this.chkUnlimited.setValue(false);
    } else if (data.products_max_order_quantity <= 0) {
      this.txtMaxOrderQuantity.disable();
      this.txtMaxOrderQuantity.setValue('');
      this.chkUnlimited.setValue(true);
    }
    
    this.cboProductsType.disable();
  },
  
  getProductsType: function() {
    return this.cboProductsType.getValue();
  }
});
Toc.products.DownloadablesPanel = function(config) {
  config = config || {};
  
  config.title = 'Downloadable Product Options';
  config.layout = 'form';
  config.labelSeparator = ' ';
  config.style = 'padding: 10px';
  config.labelWidth = 180;
  
  config.items =this.buildForm();
  
  this.addEvents({'fileupload': true});
  this.on('fileupload', this.changeState, this);
  
  Toc.products.DownloadablesPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.DownloadablesPanel, Ext.Panel, {
  buildForm: function() {
    this.file = new Ext.form.FileUploadField({
      fieldLabel: 'File:', 
      name: 'downloadable_file', 
      width: 290, 
      allowBlank: false,
      buttonText: '...'
    });

    this.sampleFile = new Ext.form.FileUploadField({
      fieldLabel: 'Sample File:', 
      name: 'sample_downloadable_file', 
      width: 290, 
      buttonText: '...'
    }); 

    this.txtNumOfDownloads = new Ext.form.TextField({
      fieldLabel: 'Number of downloads:', 
      name: 'number_of_downloads', 
      allowBlank: false,
      width: 250
    }); 

    this.txtNumOfAccessibleDays = new Ext.form.TextField({
      fieldLabel: 'Number of Accessible Days:', 
      name: 'number_of_accessible_days', 
      allowBlank: false,
      width: 250
    });

    return [this.file, 
            {xtype: 'panel', name: 'products_file', id: 'products_file_link_panel', border: false, html: ''},
            this.sampleFile, 
            {xtype: 'panel', name: 'products_sample_file', id: 'products_sample_file_link_panel', border: false}, 
            this.txtNumOfDownloads, 
            this.txtNumOfAccessibleDays];
  },
  
  changeState: function(status) {
    if (status == true) {
      this.file.setValue(' ');
      this.file.disable();
    } else {
      this.file.enable();
    }
  },
  
  loadForm: function(data) {
    htmFile = '<a href="' + data.cache_filename_url + '" target="_blank" style="padding-left:190px;padding-bottom: 15px">' + data.filename + '</a>';
    htmSampleFile = '<a href="' + data.cache_sample_filename_url + '" target="_blank" style="padding-left:190px;padding-bottom: 15px">' + data.sample_filename + '</a>';
    
    this.findById('products_file_link_panel').body.update(htmFile);
    this.findById('products_sample_file_link_panel').body.update(htmSampleFile);
            
    this.txtNumOfDownloads.setValue(data.number_of_downloads);
    this.txtNumOfAccessibleDays.setValue(data.number_of_accessible_days);
  }
});
Toc.products.GiftCertificatesPanel = function(config) {
  config = config || {};
  
  config.title = 'Gift Certificate Options';
  config.layout = 'form';
  config.labelSeparator = ' ';
  config.style = 'padding: 10px';
  config.labelWidth = 180;
  
  config.items = this.buildForm();
  
  Toc.products.GiftCertificatesPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.GiftCertificatesPanel, Ext.Panel, {
  buildForm: function() {
    this.rdoEmail = new Ext.form.Radio({
      fieldLabel: 'Gift Certificate Type:', 
      name: 'gift_certificates_type', 
      boxLabel: 'Email Gift Certificate', 
      inputValue: '0', 
      checked: true
    });    
    
    this.rdoPhysical = new Ext.form.Radio({
      fieldLabel: ' ', 
      name: 'gift_certificates_type', 
      boxLabel: 'Physical Gift Certificate', 
      inputValue: '1',
      listeners: {
        check: function(rdo, checked) {
          if (checked == true) {
            this.onCertificateTypeChange('1');
          } else {
            this.onCertificateTypeChange('0');          
          }
        },
        scope: this
      }
    });
    
    this.rdoFixAmount = new Ext.form.Radio({
      fieldLabel: 'Gift Certificate Amount Type:', 
      name: 'gift_certificates_amount_type', 
      boxLabel: 'Fix Amount', 
      inputValue: '0', 
      checked: true
    });    
    
    this.rdoOpenAmount = new Ext.form.Radio({
      fieldLabel: ' ', 
      name: 'gift_certificates_amount_type', 
      boxLabel: 'Open Amount', 
      inputValue: '1',
      listeners: {
        check: function(rdo, checked) {
          if (checked == true) {
            this.onCertificateAmountTypeChange('1');
          } else {
            this.onCertificateAmountTypeChange('0');          
          }
        },
        scope: this
      }
    });
    
    this.txtMinValue = new Ext.form.TextField({
      fieldLabel: 'Open Amount Min. Value:', 
      name: 'open_amount_min_value', 
      width: 180
    });
    
    this.txtMaxValue = new Ext.form.TextField({
      fieldLabel: 'Open Amount Max. Value:', 
      name: 'open_amount_max_value', 
      width: 180
    });
    
    this.txtMinValue.disable();
    this.txtMaxValue.disable();    
    
    return [this.rdoEmail, this.rdoPhysical, this.rdoFixAmount, this.rdoOpenAmount, this.txtMinValue, this.txtMaxValue];
  },
  
  onCertificateTypeChange: function(type) {
    if(type == '0') {
      this.rdoPhysical.setValue(false);
      this.rdoEmail.setValue(true);
    } else {
      this.rdoPhysical.setValue(true);
      this.rdoEmail.setValue(false);
    }
  },
    
  onCertificateAmountTypeChange: function(type) {
    if(type == '0') {
      this.rdoOpenAmount.setValue(false);
      this.rdoFixAmount.setValue(true);
          
      this.txtMinValue.setValue('');
      this.txtMaxValue.setValue('');  
      this.txtMinValue.disable();
      this.txtMaxValue.disable();  
      
      this.owner.txtPriceNet.enable();
      this.owner.txtPriceGross.enable();        
    } else {
      this.rdoOpenAmount.setValue(true);
      this.rdoFixAmount.setValue(false);
          
      this.txtMinValue.enable();
      this.txtMaxValue.enable();
      
      this.owner.txtPriceNet.disable();
      this.owner.txtPriceGross.disable();
    }
  },
  
  loadForm: function(data) {
    this.onCertificateTypeChange(data.gift_certificates_type);
    this.onCertificateAmountTypeChange(data.gift_certificates_amount_type);
    
    if (data.gift_certificates_amount_type == '1') {
      this.txtMinValue.setValue(data.open_amount_min_value);
      this.txtMaxValue.setValue(data.open_amount_max_value);
    } 
  }
});Toc.products.CategoriesPanel = function(config) {
  config = config || {};
  
  config.title = 'Categories';
  config.layout = 'border';
  config.style = 'padding: 5px';
  config.treeLoaded = false;
  config.items = this.buildForm();
  
  Toc.products.CategoriesPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.CategoriesPanel, Ext.Panel, {
  buildForm: function() {
    this.pnlCategoriesTree = new Ext.ux.tree.CheckTreePanel({
      region: 'center',
      name: 'categories', 
      bubbleCheck: 'none',
      cascadeCheck: 'none',
      autoScroll: true,
      border: false,
      bodyStyle: 'background-color:white;',
      rootVisible: false,
      anchor: '-24 -60',
      root: {
        nodeType: 'async',
        text: 'root',
        id: 'root',
        expanded: true,
        uiProvider: false
      },
      loader: new Ext.tree.TreeLoader({
        dataUrl: Toc.CONF.CONN_URL,
        preloadChildren: true, 
        baseParams: {
          module: 'products',
          action: 'get_categories_tree'
        },
        listeners: {
          load: function() {
            this.treeLoaded = true;
          },
          scope: this
        }
      })
    });  
    
    return this.pnlCategoriesTree;    
  },
  
  setCategories: function(categoryId) {
    if (this.treeLoaded == true) {
      this.pnlCategoriesTree.setValue(categoryId);
    } else {
      this.pnlCategoriesTree.loader.on('load', function(){
        this.pnlCategoriesTree.setValue(categoryId);
      }, this);
    }    
  },
  
  getCategories: function() {
    return this.pnlCategoriesTree.getValue();
  }
});
Toc.products.ImagesGrid = function(config) {

  config = config || {};
  
  config.region = 'center';
  config.border = false;
  config.ds = new Ext.data.Store({
    url: Toc.CONF.CONN_URL,
    baseParams: {
      module: 'products',
      action: 'get_images',
      products_id: config.productsId
    },
    reader: new Ext.data.JsonReader({
      root: Toc.CONF.JSON_READER_ROOT,
      totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
      id: 'id'
    }, [
      'id',
      'image',
      'name',
      'size',
      'default'
    ]),
    listeners: {
      load: function() {
        this.fireEvent('imagechange', this.getStore(), this);
      },
      scope: this
    }
  });  
    
  function renderAction(value) {
    if(value == '1') {
      return '<img class="img-button btn-default" style="cursor: pointer" src="templates/default/images/icons/16x16/default.png" />&nbsp;<img class="img-button btn-delete" style="cursor: pointer" src="templates/default/images/icons/16x16/delete.png" />';
    } else {
      return '<img class="img-button btn-set-default" style="cursor: pointer" src="templates/default/images/icons/16x16/default_grey.png" />&nbsp;<img class="img-button btn-delete" style="cursor: pointer" src="templates/default/images/icons/16x16/delete.png" />';
    }
  }

  config.cm = new Ext.grid.ColumnModel([
    { header: '&nbsp;', dataIndex: 'image', align: 'center'},
    { id:'products_image_name', header: 'Images', dataIndex: 'name'},
    { header: '&nbsp;',dataIndex: 'size'},
    { header: '&nbsp;',dataIndex: 'default', width:50, renderer: renderAction, align: 'center'}
  ]);
  config.autoExpandColumn = 'products_image_name';
  
  config.tbar = [
    { 
      text: TocLanguage.btnRefresh,
      iconCls:'refresh',
      handler: this.onRefresh,
      scope: this
    }
  ];
  
  this.addEvents({'imagechange' : true});
  
  Toc.products.ImagesGrid.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.ImagesGrid, Ext.grid.GridPanel, {
  onSetDefault: function(row) {
    var record = this.getStore().getAt(row);
    var image  = Ext.isEmpty(record.get('id')) ? record.get('name') : record.get('id');   
    
    Ext.Ajax.request({
      url: Toc.CONF.CONN_URL,
      params: {
        module: 'products',
        action: 'set_default',
        image: image
      },
      callback: function(options, success, response){
        var result = Ext.decode(response.responseText);
        
        if (result.success == true) {
          this.getStore().reload();
        } else {
          Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
        }
      },
      scope: this
    }); 
  },
  
  onDelete: function(row) {
    var record = this.getStore().getAt(row);
    var image  = Ext.isEmpty(record.get('id')) ? record.get('name') : record.get('id');   
    
    Ext.MessageBox.confirm(
      TocLanguage.msgWarningTitle, 
      TocLanguage.msgDeleteConfirm,
      function(btn) {
        if (btn == 'yes') {
          Ext.Ajax.request({
            url: Toc.CONF.CONN_URL,
            params: {
              module: 'products',
              action: 'delete_image',
              image: image
            },
            callback: function(options, success, response){
              var result = Ext.decode(response.responseText);
              
              if (result.success == true) {
                this.getStore().reload();
              } else {
                Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
              }
            },
            scope: this
          });   
        }
      }, this);
  },
    
  onRefresh: function() {
    this.getStore().reload();
  },
  
  onClick:function(e, target) {
    var t = e.getTarget();
    var v = this.view;
    var row = v.findRowIndex(t);
    var action = false;

    if (row !== false) {
      var btn = e.getTarget(".img-button");
      
      if (btn) {
        action = btn.className.replace(/img-button btn-/, '').trim();
        var code = this.getStore().getAt(row).get('code');
        var title = this.getStore().getAt(row).get('title');
        
        switch(action) {
          case 'set-default':
            this.onSetDefault(row);
            break;
          case 'delete':
            this.onDelete(row);
            break;
        }
      }
    }
  }
});Toc.products.ImagesPanel = function(config) {

  config = config || {};

  config.title = 'Images';
  config.layout = 'fit';
  
  config.productsId = config.productsId || null;
  config.items = this.buildForm(config.productsId);
  
  Toc.products.ImagesPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.ImagesPanel, Ext.Panel, {

  buildForm: function(productsId) {
    this.grdImages = new Toc.products.ImagesGrid({productsId: productsId});
    pnlImages = new Ext.Panel({
      layout: 'border',
      border: false,
      items:  [{
        region:'east',
        layout:'accordion',
        split: true,
        width: 250,
        minSize: 175,
        maxSize: 400,
        border:false,
        items: [this.getImageUploadPanel(productsId), this.getLocalImagesPanel(productsId)]
      }, 
      this.grdImages
     ]
    });
    
   return pnlImages;
  },
  
  getImageUploadPanel: function(productsId) {
    var appendURl = '?module=products&action=upload_image';
    
    if (productsId > 0 ) {
      appendURl += ('&products_id=' + productsId);
    }
      
    this.pnlImagesUpload = new Ext.ux.UploadPanel({
      title: 'Remote File Upload', 
      border: false,
      id: 'products-img-upload',
      removeAllIconCls: 'remove',
      maxFileSize: 4194304,
      addText: TocLanguage.btnAdd,
      uploadText: TocLanguage.btnUpload,
      enableProgress: false,
      url: Toc.CONF.CONN_URL + appendURl
    });
    
    this.pnlImagesUpload.on('allfinished', function() {
      this.grdImages.getStore().reload();
      this.pnlImagesUpload.removeAll();
    }, this);
    
    return this.pnlImagesUpload;
  },
  
  getLocalImagesPanel: function(productsId) {
    dsLocalImages = new Ext.data.Store({
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_local_images'
      },
      reader: new Ext.data.JsonReader({
        fields: ['id', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      autoLoad: true
    });
    
    this.selLocalImages = new Ext.ux.Multiselect({
      fieldLabel:"Multiselect",
      name:"multiselect",
      style: 'padding: 5px 5px 0px 10px',
      width: 230,
      height: 220,
      store: dsLocalImages,
      legend: 'Images',
      hiddenName: 'localimages[]',
      displayField: 'text',
      valueField: 'id',
      isFormField: true
    });
    
    pnlLocalImages = new Ext.Panel({
      title: 'Local Files',
      layout: 'border',
      border: false,
      items:[
        {
          region: 'north',
          border: false,
          html: '<p class="form-info">The following images are available on the server where additional images can be uploaded via FTP. The listing can be refreshed by clicking on the Local Files link.<br /><br />Please select from the following listing which images to assign to this product.</p>'
        },  
        {
          region: 'center',
          border: false,
          items: this.selLocalImages
        }
      ],
      tbar: [{
        text: TocLanguage.btnAdd,
        iconCls: 'add',
        handler: this.onLocalImageAdd,
        scope:this
      }]   
    });
    
    return pnlLocalImages;
  },
  
  onLocalImageAdd: function() {
    var images = this.selLocalImages.getValue();
    if (Ext.isEmpty(images)) return;
    
    Ext.Ajax.request({
      url: Toc.CONF.CONN_URL, 
      params: {
        module: 'products',
        action: 'assign_local_images',
        products_id: this.productsId,
        localimages: images
      },
      callback: function(options, success, response) {
        if (success == true) {
          var result = Ext.decode(response.responseText);
          
          if (result.success == true) {
            this.grdImages.getStore().reload();
            this.selLocalImages.store.reload();
          }
        } else {
          Ext.MessageBox.alert(TocLanguage.msgErrTitle, TocLanguage.msgErrTitle);
        }
      },
      scope: this
    });
  }  
});
Toc.products.VariantDataPanel = function(config) {
  config = config || {};
  
  config.id = config.valuesId;
  config.border = false;
  config.bodyStyle = 'padding: 3px;';
  config.layout = 'form';
  config.autoScroll = true;
  config.split = true;
  this.dlgProducts = config.dlgProducts;
  config.items = this.buildForm(config.valuesId, config.data, config.downloadable);
  
  Toc.products.VariantDataPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.VariantDataPanel, Ext.Panel, {

  buildForm: function(valuesId, data, downloadable) {
    var items = [
      {
        xtype: 'fieldset',
        title: 'Data',
        labelWidth: 80,
        labelSeparator: ' ',
        autoHeight: true,
        defaults: {
          anchor: '94%'
        },
        items: [
          {
            fieldLabel: 'Quantity:',
            name: 'variants_quantity[' + valuesId + ']',
            xtype: 'numberfield',
            allowDecimals: false,
            allowNegative: false,
            value: data.variants_quantity
          },
          {
            fieldLabel: 'Net Price:',
            xtype: 'textfield',
            name: 'variants_net_price[' + valuesId + ']',
            value: data.variants_net_price
          },
          {
            fieldLabel: 'SKU:',
            xtype: 'textfield',
            name: 'variants_sku[' + valuesId + ']',
            value: data.variants_sku
          },
          {
            fieldLabel: 'Model:',
            xtype: 'textfield',
            name: 'variants_model[' + valuesId + ']',
            value: data.variants_model
          },
          {
            fieldLabel: 'Weight:',
            xtype: 'textfield',
            name: 'variants_weight[' + valuesId + ']',
            value: data.variants_weight
          }, 
          {
            layout: 'column',
            border: false,
            items:[
              {
                layout: 'form',
                labelSeparator: ' ',
                labelWidth: 80,
                border: false,
                items: [{
                  fieldLabel: 'Status:', 
                  xtype:'radio', 
                  name: 'variants_status_' + valuesId, 
                  boxLabel: 'Enabled', 
                  xtype:'radio', 
                  inputValue: '1', 
                  checked: (data.variants_status == 1 ? true: false) 
                }]
              }, 
              {
                layout: 'form',
                border: false,
                items: [{
                  boxLabel: 'Disabled', 
                  xtype:'radio', 
                  name: 'variants_status_' + valuesId, 
                  hideLabel: true, 
                  inputValue: '0', 
                  checked: (data.variants_status == 1 ? false: true) 
                }]
              }
            ]
          }
        ]
      }, 
      
      this.fsImages = new Ext.form.FieldSet({
        title: 'Images',
        labelWidth: 80, 
        labelSeparator: ' ', 
        defaults: {anchor: '94%'}, 
        autoHeight: true, 
        items: this.buildImagesPanel(valuesId, data.variants_image)
      })
    ];

    if (downloadable == true || !Ext.isEmpty(data.variants_download_filename)) {
      items.push(this.fsUpload = this.buildUploadFieldset(valuesId, data.variants_download_file, data.variants_download_filename));
    }

    //register a listener to images grid to update images panel
    this.dlgProducts.pnlImages.grdImages.getStore().on('load', this.onImagesChange, this);
    this.dlgProducts.pnlData.on('producttypechange', this.onProductTypeChange, this);

    return items;
  },
  
  buildImagesPanel: function(valuesId, selectedImage) {
    var dsImages = this.dlgProducts.pnlImages.grdImages.getStore();
    var pnlImages = {
      layout: 'column',
      border: false,
      items: []
    };
    
    if ((count = dsImages.getCount()) > 0) {
      for (var i = 0; i < count; i++ ) {
        var imageID = dsImages.getAt(i).get('id');
        var imageName = dsImages.getAt(i).get('name');
        var imagePath = dsImages.getAt(i).get('image');
        var inputValue = imageID || imageName; 
        
        var pnlImage = {
          layout: 'column',
          columnWidth: .33,
          border: false,
          items: [
            {
              layout: 'form',
              labelSeparator: ' ',
              border: false,
              items: [
                {
                  xtype: 'radio', 
                  name: 'variants_image_' + valuesId, 
                  hideLabel: true,
                  inputValue: inputValue,
                  checked: ((inputValue == selectedImage) ? true : false)
                }
              ]
            },
            {
              xtype: 'panel',
              border: false,
              html: '<div style="margin: 3px; cursor:pointer;">' + imagePath + '</div>'
            }
          ]
        };
        
        pnlImages.items.push(pnlImage);
      }
    } else {
      pnlImages.items.push({
        xtype: 'statictextfield', 
        hideLabel: true, 
        value: 'Notice: There is no image available.', 
        style: 'margin-bottom: 10px'
      });
    }
    
    return pnlImages;
  },
  
  buildUploadFieldset: function(valuesId, downloadFilePath, downloadFileName) {
    var html = '';
    var file = this.dlgProducts.pnlData.tabExtraOptions;
    if (!Ext.isEmpty(downloadFileName)) {
      html = '<a href ="' + downloadFilePath +'">' + downloadFileName + '</a>';
    }
    
    var fsDownLoad = new Ext.form.FieldSet({
      title: 'Downloadable File',
      labelWidth: 80,
      labelSeparator: ' ',
      autoHeight: true,
      defaults: {
        anchor: '95%'
      },
      items: [  
        {
          xtype: 'fileuploadfield', 
          fieldLabel: 'File:', 
          name: 'products_variants_download_' + valuesId
        },
        {xtype: 'panel',  html: html, style: 'text-align: center', border: false }
      ]
    });
    
    return fsDownLoad;
  },

  onImagesChange: function() {
    this.fsImages.removeAll();
    this.fsImages.add(this.buildImagesPanel(this.valuesId, this.data.variants_image));
  },
  
  onProductTypeChange: function (type) {
    if (type == '2') {
      this.downloadable = true;
      
      this.add(this.fsUpload = this.buildUploadFieldset(this.valuesId, this.data.variants_download_file, this.data.variants_download_filename));

      this.doLayout(); 
    } else {
      this.downloadable = false;
      
      if (!Ext.isEmpty(this.fsUpload)) {
        this.remove(this.fsUpload);
        this.doLayout();
      }
    }
  }
});Toc.products.StatusCheckColumn = function(config){
    Ext.apply(this, config);
    if(!this.id){
        this.id = Ext.id();
    }
    this.renderer = this.renderer.createDelegate(this);
};

Toc.products.StatusCheckColumn.prototype = {
    init : function(grid){
        this.grid = grid;
        this.grid.on('render', function(){
            var view = this.grid.getView();
            view.mainBody.on('mousedown', this.onMouseDown, this);
        }, this);
    },

    onMouseDown : function(e, t){
        if(t.className && t.className.indexOf('x-grid3-cc-'+this.id) != -1){
            e.stopEvent();
            
            var index = this.grid.getView().findRowIndex(t);
            var record = this.grid.getStore().getAt(index);
            
            if ( this.grid.getStore().getCount() > 1 ) {
              this.grid.getStore().each(function(item) {
                if (item.get(this.dataIndex) && item != record) {
                  item.set(this.dataIndex, !item.data[this.dataIndex]);
                  item.commit();
                }
              }, this);
            }
            record.set(this.dataIndex, !record.data[this.dataIndex]);
            this.grid.getStore().commitChanges();
        }
    },

    renderer : function(v, p, record){
        p.css += ' x-grid3-check-col-td'; 
        return '<div class="x-grid3-check-col'+(v?'-on':'')+' x-grid3-cc-'+this.id+'">&#160;</div>';
    }
};

Toc.products.VariantsPanel = function(config) {
  config = config || {};
  
  config.title = 'Variants';
  config.layout = 'border';
  
  this.groupIds = [];
  this.variantsValues = [];
  this.productsId = config.productsId || null;
  this.downloadable = false;
  this.dlgProducts = config.dlgProducts;
  
  config.items = this.buildForm(config.productsId);

  this.addEvents({'variantschange' : true});    
  
  Toc.products.VariantsPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.VariantsPanel, Ext.Panel, {

  buildForm: function(productsId) {
    this.pnlVariantGroups = new Ext.Panel({
      width: 190,
      split: true,
      layout: 'form',
      border: false,
      region: 'west',
      labelAlign: 'top',
      autoScroll: true,
      tbar: [{
        text: 'Manage Variants Groups',
        iconCls : 'add',
        handler: this.onBtnManageVariantsGroupsClick,
        scope: this
      }]
    });
 
    this.grdVariants = this.buildGrdVariants(productsId);
    this.pnlVariantDataContainer = this.buildVariantDataPanel();
    
    return [this.pnlVariantGroups, this.grdVariants, this.pnlVariantDataContainer];
  },
  
  
  buildGrdVariants: function(productsId) {
    var rowActions = new Ext.ux.grid.RowActions({
      actions: [
        {iconCls: 'icon-delete-record', qtip: TocLanguage.tipDelete}
      ],
      widthIntercept: Ext.isSafari ? 4 : 2
    });
    rowActions.on('action', this.onRowAction, this);
    
    var checkColumn = new Toc.products.StatusCheckColumn({
      header: 'Default',
      textAlign: 'center',
      width: 50,
      dataIndex: 'default'
    });
    
    var dsVariants = new Ext.data.Store({
      url: Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        products_id: productsId,
        action: 'get_variants_products'        
      },
      reader: new Ext.data.JsonReader({
        root: Toc.CONF.JSON_READER_ROOT,
        totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
        id: 'products_variants_id'
      }, [
        'products_variants_id',
        'variants_values',
        'variants_groups',
        'variants_values_name',
        'data',
        'default'
      ]),
      listeners: {
        load: this.onDsVariantsLoad,
        scope: this
      }
    }); 
    
    var grdVariants = new Ext.grid.GridPanel({
      region: 'center',
      border: false,
      plugins: [rowActions, checkColumn],
      ds: dsVariants,
      cm:  new Ext.grid.ColumnModel([
        {id: 'variants_values_name', header: 'Variants', dataIndex: 'variants_values_name'},
        checkColumn,
        rowActions
      ]),
      autoExpandColumn: 'variants_values_name'
    });
    
    grdVariants.getSelectionModel().on('rowselect', this.onGrdVariantsRowSelect, this);
    
    return grdVariants;
  },

  onDsVariantsLoad: function() {
    if (this.grdVariants.getStore().getCount() > 0) {
      this.grdVariants.getStore().each(function(record) {
        this.pnlVariantDataContainer.add(this.buildVariantDataCard(record.get('variants_values'), record.get('data')));
      }, this);
      
      var record = this.grdVariants.getStore().getAt(0);
      this.generatePnlVariantsGroups(record.get('variants_groups'));
      var variantsValuesArray = record.get('variants_values').split('-');
      
      Ext.each(variantsValuesArray, function(value) {
        this.groupIds.push(value.split('_')[0]);
      }, this);
      
      this.grdVariants.getSelectionModel().selectFirstRow();

      var cardID = record.get('variants_values');
      this.pnlVariantDataContainer.getLayout().setActiveItem(cardID);
      this.setVariantsValues(record.get('variants_groups'));
        
      this.pnlVariantDataContainer.doLayout();
      this.dlgProducts.doLayout();
    }
  },
  
  onGrdVariantsRowSelect: function(sm, row, record) {
    var cardID = record.get('variants_values');
    this.pnlVariantDataContainer.getLayout().setActiveItem(cardID);
    this.setVariantsValues(record.get('variants_groups'));
  
    this.pnlVariantDataContainer.doLayout();
    this.dlgProducts.doLayout();
  },
  
  buildVariantDataPanel: function() {
    this.pnlVariantDataContainer = new Ext.Panel({
      layout:'card',
      region: 'east',
      width: 300,
      autoScroll: true,
      split: true,
      layoutOnCardChange: true,
      border:false
    });  
    
    return this.pnlVariantDataContainer;
  },

  onProductTypeChange: function (type) {
    this.enable();
    this.downloadable = false;
     
    if (type == '2') {
      this.enable();
      this.downloadable = true;  
    } else if (type == '3') {
      this.disable();
      this.downloadable = false;
    } 
  },
  
  buildVariantDataCard: function(valuesId, data) {
    var card = new Toc.products.VariantDataPanel({
      valuesId: valuesId, 
      data: data, 
      downloadable: this.downloadable, 
      dlgProducts: this.dlgProducts
    }); 
    
    return card;   
  },
  
  onBtnManageVariantsGroupsClick: function() {
    var dlg = this.owner.createVariantsGroupDialog(this.groupIds);
    
    dlg.on('groupChange', function(groups) {
      if (this.groupIds.length === 0) {
        this.generatePnlVariantsGroups(groups);
      } else {
        var ids = [];
        Ext.each(groups, function(group) {
          ids.push(group.id);
        });
        
        if ( this.groupIds.sort().toString() != ids.sort().toString()) {
          Ext.MessageBox.confirm(
            TocLanguage.msgWarningTitle, 
            'Do you really want to change the variants groups?',
            function(btn) {
              if (btn == 'yes') {
                this.deleteVariants();
                this.generatePnlVariantsGroups(groups);
              }
            }, this);
        }
      }
    }, this);
    
    dlg.show();
  },
  
  setVariantsValues: function(variants_groups) {
    Ext.each(variants_groups, function(group){
      this.pnlVariantGroups.find('name', group.name + '_' + group.id)[0].setValue(group.value);
      this.pnlVariantGroups.find('name', group.name + '_' + group.id)[0].setRawValue(group.rawvalue);
    }, this);
  },
  
  generatePnlVariantsGroups: function(groups) {
    this.groupIds = [];
    this.deletePnlVariants();
    
    if (groups.length > 0) {
      for(var i = 0 ; i < groups.length; i ++) {
        var cboVariants = {
          xtype: 'combo',
          store: new Ext.data.Store({
            url: Toc.CONF.CONN_URL,
            baseParams: {
              module: 'products',
              action: 'get_variants_values',
              group_id: groups[i].id 
            },
            reader: new Ext.data.JsonReader ({
              fields: ['id', 'text'],
              root: Toc.CONF.JSON_READER_ROOT
            }),
            autoLoad: true
          }),
          fieldLabel: groups[i].name,
          valueField: 'id',
          displayField: 'text',
          name: groups[i].name + '_' + groups[i].id,
          triggerAction: 'all',
          editable: false
        };
        
        this.groupIds.push(groups[i].id);
        this.pnlVariantGroups.add(cboVariants);
      }
      
      this.pnlVariantGroups.add(new Ext.Button({
        text: TocLanguage.btnAdd,
        iconCls: 'add',
        handler: this.addProductVariant,
        style: 'padding-top: 5px; padding-left: 110px;',
        scope: this
      }));
    }
    
    this.pnlVariantGroups.doLayout();
  },
  
  addProductVariant: function() {
    var error = false;
    var values = [];
    var names = [];  
    var groups = [];

    //get variants values
    Ext.each(this.pnlVariantGroups.findByType('combo'), function(item) {
      if (Ext.isEmpty(item.getRawValue())) {
        error = true;  
      } else {
        var values_id = item.getValue();
        var groups_id = item.getName().split('_')[1];
        
        var values_name = item.getRawValue();
        var groups_name = item.getName().split('_')[0];
        
        values.push(groups_id + '_' + values_id);
        names.push(groups_name + ': ' + values_name);
        groups.push({id: groups_id, name: groups_name, rawvalue: values_name, value: values_id});
      }
    });
    
    if (error === true) {
      Ext.MessageBox.alert(TocLanguage.msgErrTitle, 'Please choose a variant value for each variant group.');
      return;
    }
    
    //check whether variants combination exist
    //
    variants_values = values.sort().join('-');
    store = this.grdVariants.getStore();
    found = false;
    
    store.each(function(record, index) {
      var tmp = record.get('variants_values');
      
      if (tmp == variants_values) {
        found = true;
        this.grdVariants.getSelectionModel().selectRow(index);
      }
    } ,this);
    
    if (found == true) {
      Ext.MessageBox.alert(TocLanguage.msgErrTitle, 'The variant does already exist.');
      return;
    }
    
    //add record
    var record = Ext.data.Record.create([{name: 'products_variants_id'},
                                         {name: 'variants_values'},
                                         {name: 'variants_groups'},
                                         {name: 'variants_values_name'},
                                         {name: 'data'},
                                         {name: 'default'}]);

    var data = {
      variants_quantity: 0,
      variants_net_price: 0,
      variants_sku: '',
      variants_model: '',
      variants_weight: 0,
      variants_status: 0,
      variants_image: null,
      variants_download_file: null,
      variants_download_filename: null
    };
    
    store.add(new record({
      products_variants_id: -1, 
      variants_values: variants_values,
      variants_groups: groups, 
      variants_values_name: names.join('; '),
      data: data, 
      'default': ((store.getCount() > 0) ? 0 : 1)
    }));
    
    this.pnlVariantDataContainer.add(this.buildVariantDataCard(variants_values, data));
    this.grdVariants.getSelectionModel().selectLastRow();
  },
  
  onRowAction: function(grid, record, action, row, col) {
    switch(action) {
      case 'icon-delete-record':
        this.onDelete(record);
        break;
    }
  },
  
  onDelete: function(record) {
    Ext.MessageBox.confirm(
      TocLanguage.msgWarningTitle, 
      TocLanguage.msgDeleteConfirm, 
      function(btn) {
        if ( btn == 'yes' ) {
          this.grdVariants.getStore().remove(record);
          var cardID = record.get('variants_values');
          
          if (this.pnlVariantDataContainer.findById(cardID)) {
            this.pnlVariantDataContainer.remove(cardID);
          }

          this.grdVariants.getSelectionModel().selectFirstRow();
          this.pnlVariantDataContainer.doLayout(); 
          this.dlgProducts.doLayout(); 
        }
      }, this);
  },
  
  deletePnlVariants: function() {
    this.pnlVariantGroups.items.each(function(item) {
      var el = item.el.up('.x-form-item');
      
      if (el) {
        this.pnlVariantGroups.remove(item, true);
        el.remove();
      }
    }, this);
    
    this.pnlVariantGroups.removeAll();
  },
  
  deleteVariants: function() {
    this.deletePnlVariants();
    this.grdVariants.getStore().removeAll();
    this.pnlVariantDataContainer.removeAll();
  },
  
  getVariants: function() {
    var data = [];

    this.grdVariants.getStore().each(function(record) {
      var is_default = 0;
      if (record.get('default')) {
        is_default = 1;
      }
      data.push(record.get('variants_values') + ':' + record.get('products_variants_id') + ':' + is_default);
    });
    
    return data.join(';');
  },
  
  checkStatus: function() {
    var selected = false;
    var store = this.grdVariants.getStore();
    
    if (this.disabled == true) {
      selected = true;
    } else {
      if (store.getCount() > 0) {
        for (var i =0; i < store.getCount(); i++) {
          if (store.getAt(i).get('default') == '1') {
            selected = true;
            break;
          }
        }
      } else {
        selected = true;
      }
    }
    
    return selected;  
  }
});
Toc.products.XsellProductsGrid = function(config) {

  config = config || {};
  
  config.title = 'Xsell Products';

  config.productsId = config.productsId || null;
  
  config.ds = new Ext.data.Store({
    url: Toc.CONF.CONN_URL,
    baseParams: {
      module: 'products',
      action: 'get_xsell_products',
      products_id: config.productsId
    },
    reader: new Ext.data.JsonReader({
      root: Toc.CONF.JSON_READER_ROOT,
      totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
      id: 'products_id'
    }, [
       'products_id'
      ,'products_name'
    ]),
    autoLoad: true
  });
  
  config.rowActions = new Ext.ux.grid.RowActions({
    actions:[{iconCls: 'icon-delete-record', qtip: TocLanguage.tipDelete}],
    widthIntercept: Ext.isSafari ? 4 : 2
  });
  config.rowActions.on('action', this.onRowAction, this);    
  config.plugins = config.rowActions;
  
  config.sm = new Ext.grid.RowSelectionModel({ singleSelect: true });
  config.cm = new Ext.grid.ColumnModel([
    new Ext.grid.RowNumberer(),
    {id:'xsell_products_name', header: 'Products', dataIndex: 'products_name'},
    config.rowActions
  ]);
  config.autoExpandColumn = 'xsell_products_name';
  
  this.cboProducts = new Ext.form.ComboBox({
    name: 'xsellproducts',
    store: new Ext.data.Store({
      reader: new Ext.data.JsonReader({
        root: Toc.CONF.JSON_READER_ROOT,
        totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
        fields: ['id', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_products',
        products_id: config.productsId
      }
    }),
    displayField: 'text',
    valueField: 'id',
    triggerAction: 'all',
    selectOnFocus: true,
    editable: false,
    pageSize: Toc.CONF.GRID_PAGE_SIZE,
    emptyText: 'Xsell Products',
    width: 400
  });
  
  config.tbar = [
    { 
      text: TocLanguage.btnRefresh,
      iconCls:'refresh',
      handler: this.onRefresh,
      scope: this
    }, 
    '->', 
    this.cboProducts, 
    ' ', 
    {
      text: 'Insert',
      iconCls : 'add',
      handler: this.addProduct,
      scope: this
    }
  ];
  
  Toc.products.XsellProductsGrid.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.XsellProductsGrid, Ext.grid.GridPanel, {
  addProduct: function() {
    var productId = this.cboProducts.getValue().toString();
    var productName = this.cboProducts.getRawValue().toString();

    if (!Ext.isEmpty(productId)) {
      store = this.getStore();
      
      if (store.findExact('products_id', productId) == -1) {
        var record = Ext.data.Record.create([
          {name: 'products_id', type: 'string'},
          {name: 'products_name', type: 'string'}
        ]);
  
        var v = new record({
          products_id: productId,
          products_name: productName
        });
        
        store.add(v);
      }
    }
  },
  
  onRowAction: function(grid, record, action, row, col) {
    switch(action) {
      case 'icon-delete-record':
        this.getStore().removeAt(row);
        break;
    }
  },
    
  onRefresh: function() {
    this.getStore().reload();
  },
  
  getXsellProductIds: function() {
    var batch = [];
    
    this.getStore().each(function(record) {
      batch.push(record.get('products_id'));
    });
    
    return batch.join(';');
  }
});Toc.products.AttributesPanel = function(config) {

  config = config || {};
  
  config.title = 'Attributes';
  config.layout = 'form';
  config.border = false;
  
  config.productsId = config.productsId || null;
  this.buildForm(config.productsId);
  
  this.cboAttributeGroups = new Ext.form.ComboBox({
    name: 'attributeGroups',
    hiddenName: 'products_attributes_groups_id',
    store: new Ext.data.Store({
      reader: new Ext.data.JsonReader({
        root: Toc.CONF.JSON_READER_ROOT,
        totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
        fields: ['id', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_attribute_groups'
      },
      autoLoad: true
    }),
    displayField: 'text',
    valueField: 'id',
    triggerAction: 'all',
    selectOnFocus: true,
    editable: false,
    emptyText: '-- None --',
    width: 300,
    listeners: {
      select: this.onAttributeGroupsChange,
      scope: this
    }    
  });
  config.tbar = [this.cboAttributeGroups];

  Toc.products.AttributesPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.AttributesPanel, Ext.Panel, {
 
  updateAttributesPnl: function(attributes) {
    Ext.each(attributes, function(attribute, i){
      if (attribute.module == 'pull_down_menu') {
        var data = [];
        var values = attribute.value.split(',');

        Ext.each(values, function(value, i) {
          data.push([(i+1), value]);
        });
      
        var cboAttribute = new Ext.form.ComboBox({
          name: 'products_attributes_select_' + attribute.products_attributes_values_id,
          fieldLabel: attribute.name,
          labelStyle: 'padding-left: 10px',
          hiddenName: 'products_attributes_select[' + attribute.products_attributes_values_id + ']',
          store: new Ext.data.SimpleStore({
            fields: ['id', 'text'],
            data : data
          }),
          mode: 'local',
          displayField: 'text',
          valueField: 'id',
          triggerAction: 'all',
          readOnly: true,
          width: 200,
          allowblank: false,
          value: attribute.choosed_value
        });
        
        this.add(cboAttribute);
      } else if (attribute.module == 'text_field') {
        Ext.each(Toc.Languages, function(l, i){
          var txtField = new Ext.form.TextField({
            name: attribute.products_attributes_values_id,
            name: 'products_attributes_text[' + attribute.products_attributes_values_id + '][' + l.id + ']',
            value: attribute.lang_values[l.id],
            fieldLabel: ((i == 0) ? (attribute.name + ':') : '&nbsp;'),
            labelStyle: 'background: url(../images/worldflags/' + l.country_iso + '.png) no-repeat right center !important; padding-left: 10px',
            labelSeparator: ' ',
            width: 200
          });
          
          this.add(txtField);
        }, this);
      }
    }, this);
    
    this.doLayout();
  },
    
  buildForm: function(productsId) {
    if (productsId != null) {
      Ext.Ajax.request({
        url: Toc.CONF.CONN_URL, 
        params: { 
          module: 'products',
          action: 'get_attributes',
          products_id: productsId
        },
        callback: function(options, success, response) {
          if (success == true) {
            var result = Ext.decode(response.responseText);
            if (result.success == true) {
              this.cboAttributeGroups.setRawValue(result.products_attributes_groups_id);
              this.updateAttributesPnl(result.attributes);
            }
          } else {
            Ext.MessageBox.alert(TocLanguage.msgErrTitle, TocLanguage.msgErrTitle);
          }
        },
        scope: this
      });
    }
  }, 
  
  setAttributesGroupsId: function(products_attributes_groups_id) {
    this.cboAttributeGroups.setValue(products_attributes_groups_id);
  },
  
  
  onAttributeGroupsChange: function() {
    this.items.each(function(item){
      var el = item.el.up('.x-form-item');
      this.remove(item, true);
      el.remove();
    }, this);
    this.doLayout();

		var groupsId = this.cboAttributeGroups.getValue();
  	if(groupsId != '0') {
      Ext.Ajax.request({
        url: Toc.CONF.CONN_URL, 
        params: { 
          module: 'products',
          action: 'get_attributes',
          products_attributes_groups_id: groupsId
        },
        callback: function(options, success, response) {
          if (success == true) {
            var result = Ext.decode(response.responseText);
            
            if (result.success == true) {
              this.updateAttributesPnl(result.attributes);
            }
          } else {
            Ext.MessageBox.alert(TocLanguage.msgErrTitle, TocLanguage.msgErrTitle);
          }
        },
        scope: this
      });
  	}
  }
});
Toc.products.ProductDialog = function(config) {
  config = config || {};
  
  config.id = 'products-dialog-win';
  config.title = 'New Product';
  config.layout = 'fit';
  config.width = 870;
  config.height = 540;
  config.modal = true;
  config.iconCls = 'icon-products-win';
  config.productsId = config.products_id || null;
  this.owner = config.owner || null;
  this.flagContinueEdit = false;
  
  config.items = this.buildForm(config.productsId);
  
  config.buttons = [
    {
      text: TocLanguage.btnSaveAndContinue,
      handler: function(){
        this.flagContinueEdit = true;
        
        this.submitForm();
      },
      scope:this
    },
    {
      text: TocLanguage.btnSubmit,
      handler: function(){
        this.submitForm();
      },
      scope:this
    },
    {
      text: TocLanguage.btnClose,
      handler: function(){
        this.close();
      },
      scope:this
    }
  ];
    
  this.addEvents({'saveSuccess': true});      

  Toc.products.ProductDialog.superclass.constructor.call(this, config);
}

Ext.extend(Toc.products.ProductDialog, Ext.Window, {
  buildForm: function(productsId) {
    this.pnlData = new Toc.products.DataPanel();
    this.pnlVariants = new Toc.products.VariantsPanel({owner: this.owner, productsId: productsId, dlgProducts: this}); 
    this.pnlXsellProducts = new Toc.products.XsellProductsGrid({productsId: productsId});
    this.pnlAttributes = new Toc.products.AttributesPanel({productsId: productsId});
    this.pnlAttachments = new Toc.products.AttachmentsPanel({productsId: productsId, owner: this.owner});
    this.pnlCustomizations = new Toc.products.CustomizationsPanel({productsId: productsId, owner: this.owner});
    this.pnlImages = new Toc.products.ImagesPanel({productsId: productsId}); 
    
    this.pnlData.on('producttypechange', this.pnlVariants.onProductTypeChange, this.pnlVariants);
    this.pnlVariants.on('variantschange', this.pnlData.onVariantsChange, this.pnlData);
    
    this.pnlAccessories = new Toc.products.AccessoriesPanel({productsId: productsId});
    
    tabProduct = new Ext.TabPanel({
      activeTab: 0,
      defaults:{
        hideMode:'offsets'
      },
      deferredRender: false,
      items: [
        new Toc.products.GeneralPanel(), 
        this.pnlMeta = new Toc.products.MetaPanel(),
        this.pnlData,
        this.pnlCategories = new Toc.products.CategoriesPanel({productsId: productsId}),
        this.pnlImages,
        this.pnlVariants, 
        this.pnlAttributes, 
        this.pnlXsellProducts,
        this.pnlCustomizations,
        this.pnlAttachments,
        this.pnlAccessories
      ]
    }); 

    this.frmProduct = new Ext.form.FormPanel({
      layout: 'fit',
      fileUpload: true,
      url: Toc.CONF.CONN_URL,
      labelWidth: 120,
      baseParams: {  
        module: 'products',
        action: 'save_product'
      },
      items: tabProduct
    });

    return this.frmProduct;
  },
    
  show: function(categoryId) {
    this.frmProduct.form.reset();  

    this.pnlImages.grdImages.store.load();
    this.pnlVariants.grdVariants.store.load();
    
    if (this.productsId > 0) {
      this.frmProduct.load({
        url: Toc.CONF.CONN_URL,
        params:{
          action: 'load_product',
          products_id: this.productsId
        },
        success: function(form, action) {
          this.pnlData.onPriceNetChange(); 
          this.pnlData.updateCboTaxClass(action.result.data.products_type);
          this.pnlData.loadExtraOptionTab(action.result.data);   
          this.pnlCategories.setCategories(action.result.data.categories_id);
          this.pnlVariants.onProductTypeChange(action.result.data.products_type);
          this.pnlAttributes.setAttributesGroupsId(action.result.data.products_attributes_groups_id);
          
          Toc.products.ProductDialog.superclass.show.call(this);
        },
        failure: function(form, action) {
          Ext.Msg.alert(TocLanguage.msgErrTitle, TocLanguage.msgErrLoadData);
        },
        scope: this       
      });
    } else {   
      Toc.products.ProductDialog.superclass.show.call(this);
    }
    
    if (!Ext.isEmpty(categoryId) && (categoryId > 0)) {
      this.pnlCategories.setCategories(categoryId);
    }
  },

  submitForm: function() {
    var params = {
      action: 'save_product',
      accessories_ids: this.pnlAccessories.getAccessoriesIds(),
      xsell_ids: this.pnlXsellProducts.getXsellProductIds(),
      products_variants: this.pnlVariants.getVariants(), 
      products_id: this.productsId,
      attachments_ids: this.pnlAttachments.getAttachmentsIDs(),
      categories_id: this.pnlCategories.getCategories(),
      customization_fields: this.pnlCustomizations.getCustomizations()
    };
    
        
    if (this.productsId > 0) {
      params.products_type = this.pnlData.getProductsType();
    }
    
    var status = this.pnlVariants.checkStatus();
    
    if (status == true) { 
      this.frmProduct.form.submit({
        params: params,
        waitMsg: TocLanguage.formSubmitWaitMsg,
        success:function(form, action){
          this.fireEvent('saveSuccess', action.result.feedback);

          if (this.flagContinueEdit == true) {
            this.productsId = action.result.productsId;
            this.frmProduct.form.baseParams['products_id'] = this.productsId;
            this.pnlImages.grdImages.getStore().baseParams['products_id'] = this.productsId;
            this.pnlImages.pnlImagesUpload.uploader.setUrl(Toc.CONF.CONN_URL + '?module=products&action=upload_image&products_id=' + this.productsId);
            this.pnlImages.productsId = this.productsId;
            
            this.pnlData.cboProductsType.disable();
            this.pnlCustomizations.getStore().reload();
          
            var onDsImagesLoad = function () {
              this.pnlVariants.pnlVariantDataContainer.removeAll(true);
              this.pnlVariants.pnlVariantDataContainer.doLayout();
              this.pnlVariants.grdVariants.getStore().baseParams['products_id'] = this.productsId;
              this.pnlVariants.grdVariants.getStore().reload();       

              this.pnlImages.grdImages.getStore().removeListener('load', onDsImagesLoad, this);
            }
            
            this.pnlImages.grdImages.getStore().on('load', onDsImagesLoad, this);
            this.pnlImages.grdImages.getStore().reload();

            this.flagContinueEdit = false;  
            
            //Ext.MessageBox.alert(TocLanguage.msgSuccessTitle, action.result.feedback);
            
            Ext.each(action.result.urls, function(url) {
              this.pnlMeta.txtProductUrl[url.languages_id].setValue(url.url);
            }, this);
          } else {
            this.close();
          }
        },    
        failure: function(form, action) {
          if(action.failureType != 'client') {
            Ext.MessageBox.alert(TocLanguage.msgErrTitle, action.result.feedback);
          }
        },
        scope: this
      });  
    } else {
      Ext.MessageBox.alert(TocLanguage.msgErrTitle, 'Please select a default variant for this product.');
    }
  }
});
Toc.products.AttachmentsPanel = function(config) {
  config = config || {};
  
  config.border = false;
  config.title = 'Attachments';
  config.viewConfig = {
    emptyText: TocLanguage.gridNoRecords
  };
  
  config.ds = new Ext.data.Store({
    url: Toc.CONF.CONN_URL,
    baseParams: {
      module: 'products',
      products_id: config.productsId,
      action: 'load_products_attachments'        
    },
    reader: new Ext.data.JsonReader({
      root: Toc.CONF.JSON_READER_ROOT,
      totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
      id: 'attachments_id'
    },  [
      'attachments_id',
      'attachments_name',
      'attachments_file_name',
      'attachments_cache_filename',
      'attachments_description'
    ]),
    autoLoad: true
  }); 
  
  config.rowActions = new Ext.ux.grid.RowActions({
    actions:[
      {iconCls: 'icon-delete-record', qtip: TocLanguage.tipDelete}],
      widthIntercept: Ext.isSafari ? 4 : 2
  });
    widthIntercept: Ext.isSafari ? 4 : 2
  
  config.rowActions.on('action', this.onRowAction, this);
  config.plugins = config.rowActions;
  
  config.sm = new Ext.grid.CheckboxSelectionModel();
  config.cm = new Ext.grid.ColumnModel([
    config.sm,
    {id: 'attachments_name', header: 'Name', dataIndex: 'attachments_name'},
    {header: 'File', dataIndex: 'attachments_file_name', width: 250},
    {header: 'Description', dataIndex: 'attachments_description', width: 250},
    config.rowActions 
  ]);
  config.autoExpandColumn = 'attachments_name';
  
  config.tbar = [{
    text: TocLanguage.btnAdd,
    iconCls: 'add',
    handler: this.onAdd,
    scope: this
  }, '-', {
    text: TocLanguage.btnDelete,
    iconCls: 'remove',
    handler: this.onBatchDelete,
    scope: this
  }];
  
  Toc.products.AttachmentsPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.AttachmentsPanel, Ext.grid.GridPanel, {
  onAdd: function() {
    var dlg = this.owner.createAttachmentsListDialog(this.productsId);
    
    dlg.on('saveSuccess', function(records) {
      Ext.each(records, function(record) {
        var attachments_id = record.get('attachments_id');
        var attachments_name = record.get('attachments_name');
        var attachments_file_name = record.get('attachments_filename');
        var attachments_description = record.get('attachments_description');
 
          
        var store = this.getStore();
        if (store.find('attachments_id', attachments_id) == -1) {
          var record = Ext.data.Record.create([
            {name: 'attachments_id', type: 'int'},
            {name: 'attachments_name', type: 'string'},
            {name: 'attachments_file_name', type: 'string'},
            {name: 'attachments_description', type: 'string'}
          ]);
          
          var v = new record({attachments_id: attachments_id, attachments_name: attachments_name, attachments_file_name: attachments_file_name, attachments_description: attachments_description});
          store.add(v);
        }
      }, this);
    }, this);

    dlg.show();
  },
  
  getAttachmentsIDs: function() {
    var ids = [];

    this.getStore().each(function(record) {
      ids.push(record.get('attachments_id'));
    });

    return ids;
  },
  
  onRowAction: function(grid, record, action, row, col) {
    switch(action) {
      case 'icon-delete-record':
        this.onDelete(record);
        break;
    }
  },
  
  onDelete: function(record) {
    this.getStore().remove(record);
  },
  
  onBatchDelete: function() {
    var attachments = this.getSelectionModel().getSelections();

    if (attachments.length > 0) {
      Ext.each(attachments, function(attachment) {
        this.getStore().remove(attachment);
      }, this);
    }else{
       Ext.MessageBox.alert(TocLanguage.msgInfoTitle, TocLanguage.msgMustSelectOne);
    }
  }
});

Toc.products.AttachmentsGrid = function(config) {
  config = config || {};
  
  config.border = false;
  config.viewConfig = {
    emptyText: TocLanguage.gridNoRecords
  };
  
  config.ds = new Ext.data.Store({
    url: Toc.CONF.CONN_URL,
    baseParams: {
      module: 'products',
      action: 'list_product_attachments'        
    },
    reader: new Ext.data.JsonReader({
      root: Toc.CONF.JSON_READER_ROOT,
      totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
      id: 'attachments_id'
    },  [
      'attachments_id',
      'attachments_name',
      'attachments_filename',
      'attachments_cache_filename',
      'attachments_description'
    ]),
    autoLoad: true
  }); 
  
  config.rowActions = new Ext.ux.grid.RowActions({
    actions:[
      {iconCls: 'icon-edit-record', qtip: TocLanguage.tipEdit},
      {iconCls: 'icon-delete-record', qtip: TocLanguage.tipDelete}
    ],
    widthIntercept: Ext.isSafari ? 4 : 2
  });
  
  config.sm = new Ext.grid.CheckboxSelectionModel();
  config.plugins = config.rowActions;
  
  config.cm = new Ext.grid.ColumnModel([
    config.sm,
    {id: 'attachments_name', header: 'Name', dataIndex: 'attachments_name'},
    {header: 'File', dataIndex: 'attachments_filename', width: 250},
    {header: 'Description', dataIndex: 'attachments_description', width: 250},
    config.rowActions 
  ]);
  config.autoExpandColumn = 'attachments_name';
  config.rowActions.on('action', this.onRowAction, this);
  
  config.txtSearch = new Ext.form.TextField({
    emptyText: '--Name--'
  });
  
  config.tbar = [{
    text: TocLanguage.btnAdd,
    iconCls: 'add',
    handler: function() {
      this.onAdd();
    },
      scope: this
  },'-', {
    text: TocLanguage.btnDelete,
    iconCls: 'remove',
    handler: this.onBatchDelete,
    scope: this
  }, '-', { 
    text: TocLanguage.btnRefresh,
    iconCls: 'refresh',
    handler: this.onRefresh,
    scope: this
  }, '->', config.txtSearch, ' ',
  {
    iconCls : 'search',
    handler : this.onSearch,
    scope : this
  }];
  
  var thisObj = this;
  config.bbar = new Ext.PageToolbar({
    pageSize: Toc.CONF.GRID_PAGE_SIZE,
    store: config.ds,
    steps: Toc.CONF.GRID_STEPS,
    btnsConfig:[
      {
        text: TocLanguage.btnAdd,
        iconCls:'add',
        handler: function() {
          thisObj.onAdd();
        }
      },
      {
        text: TocLanguage.btnDelete,
        iconCls:'remove',
        handler: function() {
          thisObj.onBatchDelete();
        }
      }
    ],
    beforePageText : TocLanguage.beforePageText,
    firstText: TocLanguage.firstText,
    lastText: TocLanguage.lastText,
    nextText: TocLanguage.nextText,
    prevText: TocLanguage.prevText,
    afterPageText: TocLanguage.afterPageText,
    refreshText: TocLanguage.refreshText,
    displayInfo: true,
    displayMsg: TocLanguage.displayMsg,
    emptyMsg: TocLanguage.emptyMsg,
    prevStepText: TocLanguage.prevStepText,
    nextStepText: TocLanguage.nextStepText
  });
  
  Toc.products.AttachmentsGrid.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.AttachmentsGrid, Ext.grid.GridPanel, {
  onAdd: function(productsId, inTabAttachments) {
    var dlg = this.owner.createAttachmentsDialog();
      
    dlg.on('saveSuccess', function(){
     this.onRefresh();
    }, this);
    
    dlg.setTitle('New Attachment');
    dlg.show();
  },
  
  onEdit: function(record) {
    var dlg = this.owner.createAttachmentsDialog();
    dlg.setTitle(record.get('attachments_name'));

    dlg.on('saveSuccess', function(){
      this.onRefresh();
    }, this);
    
    dlg.show(record.get('attachments_id'));
  },
  
  onDelete: function(record) {
    var attachmentsId = record.get('attachments_id');
    var attachmentsName = record.get('attachments_cache_filename');
    
    Ext.MessageBox.confirm(
      TocLanguage.msgWarningTitle, 
      TocLanguage.msgDeleteConfirm,
      function(btn) {
        if ( btn == 'yes' ) {
          Ext.Ajax.request({
            url: Toc.CONF.CONN_URL,
            params: {
              module: 'products',
              action: 'delete_attachment',
              attachments_id: attachmentsId,
              attachments_name: attachmentsName
            }, 
            callback: function(options, success, response) {
              result = Ext.decode(response.responseText);
              
              if (result.success == true) {
                this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result.feedback});
                this.getStore().reload();
              } else {
                Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
              }
            },
            scope: this
          });   
        }
      }, 
      this
    );
  },
  
  onBatchDelete: function() {
    var selection = this.getSelectionModel().selections,
    keys = selection.keys,
    result = [];
      
    Ext.each(keys, function(key, index) {
      result = result.concat(key + ':' + selection.map[key].get('attachments_cache_filename'));
    });
  
    if (result.length > 0) {    
      var batch = result.join(',');
    
      Ext.MessageBox.confirm(
        TocLanguage.msgWarningTitle, 
        TocLanguage.msgDeleteConfirm,
        function(btn) {
          if (btn == 'yes') {
            Ext.Ajax.request({
              url: Toc.CONF.CONN_URL,
              params: {
                module: 'products',
                action: 'delete_attachments',
                batch: batch
              },
              callback: function(options, success, response){
                result = Ext.decode(response.responseText);
                
                if (result.success == true) {
                  this.owner.app.showNotification({title: TocLanguage.msgSuccessTitle, html: result.feedback});
                  this.onRefresh();
                } else {
                  Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
                }
              },
              scope: this
            });   
          }
        }, 
        this
      );
    } else { 
      Ext.MessageBox.alert(TocLanguage.msgInfoTitle, TocLanguage.msgMustSelectOne);
    }
  },
  
  onRefresh: function() {
    this.getStore().reload();
  },
  
  onSearch: function() {
    var attachments_name = this.txtSearch.getValue();
    var store = this.getStore(); 
    
    store.baseParams['attachments_name'] = attachments_name;
    store.reload();
  },
  
  onRowAction: function (grid, record, action, row, col) {
    switch (action) {
      case 'icon-delete-record':
        this.onDelete(record);
        break;
      case 'icon-edit-record':
        this.onEdit(record);
        break;
    }
  }
});

Toc.products.AttachmentsDialog = function(config) {
  config = config || {};
  
  config.id = 'products_attachments_dialog-win';
  config.width = 450;
  config.height = 300;
  config.iconCls = 'icon-products_attachments-win';
  
  config.items = this.buildForm();
  
  config.buttons = [{
    text: TocLanguage.btnSave,
    handler: function() {
      this.submitForm();
    },
    scope: this
  }, {
    text: TocLanguage.btnClose,
    handler: function() { 
      this.close();
    },
    scope: this
  }];
  
  Toc.products.AttachmentsDialog.superclass.constructor.call(this, config);
}

Ext.extend(Toc.products.AttachmentsDialog, Ext.Window, {
  show: function (id) {
    var attachmentsId = id || null;
    this.frmAttachment.form.baseParams['attachments_id'] = attachmentsId;
    
    if (attachmentsId > 0) {
      this.frmAttachment.load({
        url: Toc.CONF.CONN_URL,
        params: {
          module: 'products',
          action: 'load_attachment'
        },
        success: function (form, action) {
          Toc.products.AttachmentsDialog.superclass.show.call(this);
          var htmFile = '<a href="' + action.result.attachments_file + '" style="padding: 2px;">' + action.result.data['filename'] + '</a>';
          
          this.pnlAttachmentFile.findById('attachments_file').body.update(htmFile);
        },
        failure: function (form, action) {
          Ext.Msg.alert(TocLanguage.msgErrTitle, action.result.feedback);
        },
        scope: this
      });
    } else {
      Toc.products.AttachmentsDialog.superclass.show.call(this);
    }
  },
  
  getAttachmentFilePanel: function() {
    this.pnlAttachmentFile = new Ext.Panel({
      border: false,
      layout: 'form',
      defaults: {
        anchor: '96%'
      },
      items: [{
        xtype: 'fileuploadfield', fieldLabel: 'File',name: 'attachments_file_name'
      },{
        xtype: 'panel',
        border: false,
        id: 'attachments_file',
        style: 'margin-left: 115px; text-decoration: underline'
      }]
    });
    
    return this.pnlAttachmentFile;
  },
  
  getAttachmentDescriptionPanel: function() {
    this.tabLanguage = new Ext.TabPanel({
      activeTab: 0,
      enableTabScroll: true,
      deferredRender: false,
      border: false
    });  
    
    var pnlLangen_US = new Ext.Panel({
          labelWidth: 100,
          title:'English',
          iconCls: 'icon-us-win',
          layout: 'form',
          autoHeight: true,
          labelSeparator: ' ',
          defaults: {
            anchor: '96%'
          },
          items: [
            {xtype: 'textfield', fieldLabel: 'Name:', name: 'attachments_name[1]', allowBlank: false},
            {xtype: 'textarea', fieldLabel: 'Description:', name: 'attachments_description[1]', height: 120}
          ]
        });
        
        this.tabLanguage.add(pnlLangen_US);
            
    return this.tabLanguage;
  },

  buildForm: function() {
    this.frmAttachment = new Ext.form.FormPanel({
      border: false,
      url: Toc.CONF.CONN_URL,
      fileUpload: true,
      labelWidth: 100,
      baseParams: {  
        module: 'products',
        action: 'save_attachment'
      }, 
      layoutConfig: {
        labelSeparator: ''
      },
      items: [
        this.getAttachmentFilePanel(),
        this.getAttachmentDescriptionPanel()
      ]
    });
    
    return this.frmAttachment;
  },
  
  submitForm: function() {
    this.frmAttachment.form.submit({
      success:function(form, action) {
        this.fireEvent('saveSuccess', action.result.feedback); 
        this.close();
      },
      failure: function(form, action) {
        if (action.failureType != 'client') {         
          Ext.MessageBox.alert(TocLanguage.msgErrTitle, action.result.feedback);      
        }         
      },
      scope: this
    });
  }
});
Toc.products.AttachmentsListDialog = function(config) {
  config = config || {};
  
  config.title = 'Attachments';
  
  config.width = 500;
  config.modal = true;
  config.layout = 'fit';
  config.height = 300;
  config.border =  false;
  config.iconCls = 'icon-products_attachments-win';
  config.id = "products_attachments_list_dialog-win";
  
  config.items = this.buildGrid();
  
  config.buttons = [{
    text: TocLanguage.btnAdd,
    handler: this.onAdd,
    scope: this
  },{
    text: TocLanguage.btnClose,
    handler: function() {
      this.close();
    },
    scope: this
  }];
  
  this.addEvents('saveSuccess', true);

  Toc.products.AttachmentsListDialog.superclass.constructor.call(this, config);
}

Ext.extend(Toc.products.AttachmentsListDialog, Ext.Window, {
  buildGrid: function() {
    var dsAttachments = new Ext.data.Store({
      url: Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'list_product_attachments'     
      },
      reader: new Ext.data.JsonReader({
        root: Toc.CONF.JSON_READER_ROOT,
        totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
        id: 'attachments_id'
      },  [
        'attachments_id',
        'attachments_name',
        'attachments_filename',
        'attachments_description',
        'action'
      ]),
      autoLoad: true
    });
        
    this.txtSearch = new Ext.form.TextField({
      emptyText: '--Name--'
    });
    
    var sm = new Ext.grid.CheckboxSelectionModel();
    this.grdProductsAttachments = new Ext.grid.GridPanel({
      viewConfig: {
        emptyText: TocLanguage.gridNoRecords
      },
      border: false,
      ds: dsAttachments,
      sm: sm,
      cm: new Ext.grid.ColumnModel([
        sm,
        {id: 'attachments_name', header: 'Name', dataIndex: 'attachments_name'},
        {header: 'File', dataIndex: 'attachments_filename', width: 250},
        {header: 'Description', dataIndex: 'attachments_description'}
      ]),
      autoExpandColumn: 'attachments_name',
      
      tbar: [{
        text: TocLanguage.btnRefresh,
        iconCls: 'refresh',
        handler: this.onRefresh,
        scope: this
      }, '->', this.txtSearch, ' ',
      {
        iconCls : 'search',
        handler : this.onSearch,
        scope : this
      }],
      
      bbar: new Ext.PagingToolbar({
        pageSize: Toc.CONF.GRID_PAGE_SIZE,
        store: dsAttachments,
        iconCls: 'icon-grid',
        displayInfo: true,
        displayMsg: TocLanguage.displayMsg,
        emptyMsg: TocLanguage.emptyMsg
      })
    });    
    
    return this.grdProductsAttachments;
  },
  
  onRefresh: function() {
    this.grdProductsAttachments.getStore().reload();
  },
  
  onSearch: function() {
    var attachments_name = this.txtSearch.getValue();
    var store = this.grdProductsAttachments.getStore(); 
    
    store.baseParams['attachments_name'] = attachments_name;
    store.reload();
  },
  
  onAdd: function() {
    var attachments = this.grdProductsAttachments.getSelectionModel().getSelections();
    
    this.fireEvent('saveSuccess', attachments);    
    
    this.close();
  }
});
Toc.products.ProductsDuplicateDialog = function(config) {
  
  config = config || {};
  
  config.id = 'products_duplicate-dialog-win';
  config.layout = 'fit';
  config.width = 450;
  config.autoHeight = true;
  config.modal = true;
  config.iconCls = 'icon-products-win';

  config.items = this.buildForm(config.productsId);
  
  config.buttons = [
    {
      text:TocLanguage.btnSave,
      handler: function(){
        this.submitForm();
      }, 
      scope:this
    },
    {
      text: TocLanguage.btnClose,
      handler: function(){
        this.close();
      },
      scope:this
    }
  ];
  
  Toc.products.ProductsDuplicateDialog.superclass.constructor.call(this, config);
}

Ext.extend(Toc.products.ProductsDuplicateDialog, Ext.Window, {
  
  buildForm: function(productsId) {
    this.frmProduct = new Ext.form.FormPanel({ 
      url: Toc.CONF.CONN_URL,
      baseParams: {  
        module: 'products',
        action: 'copy_product',
        products_id: productsId
      }, 
      autoHeight: true,
      style: 'padding: 8px',
      border: false,
      defaults: {
        anchor: '97%'
      },
      layoutConfig: {
        labelSeparator: ''
      },
      labelWidth: 200,
      items: [
        {xtype: 'statictextfield', hideLabel: true, value: 'Please check the following items to choose the data that to be copied.'},
        {xtype: 'checkbox', name: 'copy_images', fieldLabel: 'Copy Product Images?', checked: true, inputValue: 1},
        {xtype: 'checkbox', name: 'copy_variants', fieldLabel: 'Copy Product Variants?', checked: true, inputValue: 1},
        {xtype: 'checkbox', name: 'copy_attributes', fieldLabel: 'Copy Products Attributes?', checked: true, inputValue: 1},
        {xtype: 'checkbox', name: 'copy_customization_fields', fieldLabel: 'Copy Product Customization Fields?', checked: true, inputValue: 1},
        {xtype: 'checkbox', name: 'copy_attachments', fieldLabel: 'Copy Product Attachments?', checked: true, inputValue: 1},
        {xtype: 'checkbox', name: 'copy_accessories', fieldLabel: 'Copy Product Accessories?', checked: true, inputValue: 1},
        {xtype: 'checkbox', name: 'copy_xsell', fieldLabel: 'Copy Cross Sell Products?', checked: true, inputValue: 1}
      ]
    });
    
    return this.frmProduct;
  },

  submitForm: function() {
    this.frmProduct.form.submit({
      waitMsg: TocLanguage.formSubmitWaitMsg,
      success: function(form, action){
        this.fireEvent('saveSuccess', action.result.feedback);
        this.close();
      },    
      failure: function(form, action) {
        if(action.failureType != 'client') {
          Ext.MessageBox.alert(TocLanguage.msgErrTitle, action.result.feedback);
        }
      },
      scope: this
    });   
  }
});
Toc.products.CustomizationsPanel = function(config) {
  config = config || {};
  
  config.border = false;
  config.title = 'Customizations';
  config.viewConfig = {
    emptyText: TocLanguage.gridNoRecords
  };
  
  config.ds = new Ext.data.Store({
    url: Toc.CONF.CONN_URL,
    baseParams: {
      module: 'products',
      products_id: config.productsId,
      action: 'list_customization_fields'        
    },
    reader: new Ext.data.JsonReader({
      root: Toc.CONF.JSON_READER_ROOT,
      totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
      id: 'customization_fields_id'
    },  [
      'customization_fields_id',
      'customization_fields_name',
      'products_id',
      'customization_type',
      'is_required',
      'name_data'
    ]),
    autoLoad: true
  }); 
  
  renderRequired = function(isRequired) {
    if(isRequired == 1) {
      return 'Yes';
    }else {
      return 'No';
    }
  };
  
  renderType = function(customizationType) {
    if(customizationType == 1) {
      return 'Input Text';
    }else {
      return 'Upload File Field';
    }
  };
  
  config.rowActions = new Ext.ux.grid.RowActions({
    actions:[
      {iconCls: 'icon-edit-record', qtip: TocLanguage.tipEdit},
      {iconCls: 'icon-delete-record', qtip: TocLanguage.tipDelete}],
      widthIntercept: Ext.isSafari ? 4 : 2
  });
  
  config.rowActions.on('action', this.onRowAction, this);
  config.plugins = config.rowActions;
  
  config.sm = new Ext.grid.CheckboxSelectionModel();
  config.cm = new Ext.grid.ColumnModel([
    config.sm,
    {id: 'customization_fields_name', header: 'Name', dataIndex: 'customization_fields_name'},
    {header: 'Type', dataIndex: 'customization_type', renderer: renderType, width: 250},
    {header: 'Is Required', dataIndex: 'is_required', renderer: renderRequired, width: 250},
    config.rowActions 
  ]);
  config.autoExpandColumn = 'customization_fields_name';
  
  config.tbar = [{
    text: TocLanguage.btnAdd,
    iconCls: 'add',
    handler: this.onAdd,
    scope: this
  },
  '-', 
  {
    text: TocLanguage.btnDelete,
    iconCls: 'remove',
    handler: this.onBatchDelete,
    scope: this
  }];
  
  Toc.products.CustomizationsPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.CustomizationsPanel, Ext.grid.GridPanel, {
  onChange: function(row, type, required, name, lanData) {
    var store = this.getStore();
    required = (required == true) ? 1 : 0;
    
    if (row == -1) {
      var record = Ext.data.Record.create([
        {name: 'customization_fields_id', type: 'int'},
        {name: 'customization_fields_name', type: 'string'},
        {name: 'products_id', type: 'string'},
        {name: 'customization_type', type: 'int'},
        {name: 'is_required', type: 'int'},
        {name: 'name_data'}
      ]);
      
      var v = new record({
        customization_fields_id: -1, 
        customization_fields_name: name, 
        products_id: this.productsId, 
        customization_type: type, 
        is_required: required, 
        name_data: Ext.encode(lanData)
      });
      
      store.add(v);
    } else {
      var v = store.getAt(row);

      v.set('customization_fields_name', name);
      v.set('products_id', this.productsId);
      v.set('customization_type', type);
      v.set('is_required', required);
      v.set('name_data', Ext.encode(lanData));
      
      store.commitChanges();
    }
  },
  
  onAdd: function() {
    var dlg = this.owner.createCustomizationsDialog({owner: this});
    
    dlg.show();
  },
  
  onEdit: function(row, record) {
    var dlg = this.owner.createCustomizationsDialog({owner: this});
    dlg.setTitle(record.get('customization_fields_name'));

    dlg.show(row, record);
  },
  
  getCustomizations: function() {
    var data = [];

    this.getStore().each(function(record) {
      data.push(record.get('customization_fields_id') + '::' + record.get('customization_type') + '::' + record.get('is_required') + '::' + record.get('name_data'));
    });

    return data.join(';;');
  },
  
  onRowAction: function(grid, record, action, row, col) {
    switch(action) {
      case 'icon-edit-record':
        this.onEdit(row, record);
        break;
      case 'icon-delete-record':
        this.onDelete(record);
        break;
    }
  },
  
  onDelete: function(record) {
    this.getStore().remove(record);
  },
  
  onBatchDelete: function() {
    var customizations = this.getSelectionModel().getSelections();

    if (customizations.length > 0) {
      Ext.each(customizations, function(customization) {
        this.getStore().remove(customization);
      }, this);
    }else{
       Ext.MessageBox.alert(TocLanguage.msgInfoTitle, TocLanguage.msgMustSelectOne);
    }
  }
});

Toc.products.CustomizationsDialog = function(config) {
  config = config || {};
  
  config.id = 'customization_fields_dialog-win';
  config.title = 'New Customization';
  config.width = 400;
  config.iconCls = 'icon-products-win';
  this.owner = config.owner;
  this.row = -1;

  config.items = this.buildForm();
  
  config.buttons = [{
    text: TocLanguage.btnSave,
    handler: function() {
      this.submitForm();
    },
    scope: this
  }, {
    text: TocLanguage.btnClose,
    handler: function() { 
      this.close();
    },
    scope: this
  }];
  
  Toc.products.CustomizationsDialog.superclass.constructor.call(this, config);
}

Ext.extend(Toc.products.CustomizationsDialog, Ext.Window, {
  show: function (row, record) {
    var record = record || null;
    
    if (record != null) {
      this.row = row;
      this.record = record;
      
      this.cboTypes.setValue(record.get('customization_type'));
      if (record.get('is_required')) {
        this.rdbRequiredYes.setValue(true);
        this.rdbRequiredNo.setValue(false);
      } else {
        this.rdbRequiredYes.setValue(false);
        this.rdbRequiredNo.setValue(true);
      }
      
      var data = Ext.decode(record.get('name_data'));
      this.txtName1.setValue(data.name1);      
      Toc.products.CustomizationsDialog.superclass.show.call(this);
    } else {
      Toc.products.CustomizationsDialog.superclass.show.call(this);
    }
  },
  
  buildForm: function() {
    this.cboTypes = new Ext.form.ComboBox({
      fieldLabel: 'Field Type:', 
      store: new Ext.data.SimpleStore({
        fields: ['id', 'text'],
        data: [
          ['1', 'Input Text'],
          ['0', 'Upload File Field']
        ]
      }), 
      displayField: 'text', 
      valueField: 'id', 
      name: 'type',
      hiddenName: 'type', 
      readOnly: true, 
      forceSelection: true,
      mode: 'local',
      value: '1',
      triggerAction: 'all'
    });
  
    this.frmCustomization = new Ext.form.FormPanel({
      border: false,
      url: Toc.CONF.CONN_URL,
      defaults: {
        anchor: '98%'
      },
      style: 'padding: 8px',
      border: false,
      labelWidth: 120,
      layoutConfig: {
        labelSeparator: ''
      },
      items: [
        this.cboTypes,
        this.txtName1 = new Ext.form.TextField({fieldLabel: "Field Name:",name: "name[1]",labelStyle: 'background: url(../images/worldflags/us.png) no-repeat right center !important;', allowBlank: false}),        {
          layout: 'column',
          border: false,
          items:[
            {
              layout: 'form',
              labelSeparator: ' ',
              labelWidth: 120,
              border: false,
              items: [
                this.rdbRequiredYes = new Ext.form.Radio({
                  fieldLabel: 'Is Required:', 
                  name: 'is_required', 
                  boxLabel: 'Yes', 
                  xtype:'radio', 
                  inputValue: '1' 
                })
              ]
            }, 
            {
              layout: 'form',
              border: false,
              items: [
                this.rdbRequiredNo = new Ext.form.Radio({
                  boxLabel: 'No', 
                  xtype:'radio', 
                  name: 'is_required', 
                  hideLabel: true, 
                  inputValue: '0',
                  checked: true
                })
              ]
            }
          ]
        }
      ]
    });
    
    return this.frmCustomization;
  },
  
  submitForm: function() {
    var data = {};
    var error = false;
    var name = '';
    
    data.name1 = this.txtName1.getValue();if(Ext.isEmpty(data.name1)) { 
              error = true;
            }name = this.txtName1.getValue();    
    if (error == false) {
      var type = this.cboTypes.getValue();
      var required = (this.rdbRequiredYes.getValue() == true) ? true : false;

      this.owner.onChange(this.row, type, required, name, data); 
      this.close();
    }
  }
});
Toc.products.AccessoriesPanel = function(config) {
  config = config || {};
  
  config.border = false;
  config.title = 'Accessories';
  
  config.productsId = config.productsId || null;
  
  config.ds = new Ext.data.Store({
    url: Toc.CONF.CONN_URL,
    baseParams: {
      module: 'products',
      action: 'get_accessories',
      products_id: config.productsId
    },
    reader: new Ext.data.JsonReader({
      root: Toc.CONF.JSON_READER_ROOT,
      totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
      id: 'accessories_id'
    },  [
      'accessories_id',
      'products_name'
    ]),
    autoLoad: true
  }); 
  
  config.rowActions = new Ext.ux.grid.RowActions({
    actions:[
      {iconCls: 'icon-delete-record', qtip: TocLanguage.tipDelete}],
      widthIntercept: Ext.isSafari ? 4 : 2
  });
  config.rowActions.on('action', this.onRowAction, this);
  config.plugins = config.rowActions;
  
  config.sm = new Ext.grid.RowSelectionModel({ singleSelect: true });
  config.cm = new Ext.grid.ColumnModel([
    new Ext.grid.RowNumberer(),
    {id: 'accessories_products_name', header: 'Products', dataIndex: 'products_name'},
    config.rowActions 
  ]);
  config.autoExpandColumn = 'accessories_products_name';
  config.viewConfig = {emptyText: TocLanguage.gridNoRecords};
    
  config.cboProducts = new Ext.form.ComboBox({
    name: 'accessories_name',
    store: new Ext.data.Store({
      reader: new Ext.data.JsonReader({
        root: Toc.CONF.JSON_READER_ROOT,
        totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
        fields: ['id', 'text'],
        root: Toc.CONF.JSON_READER_ROOT
      }),
      url:Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'get_products',
        products_id: config.productsId
      }
    }),
    displayField: 'text',
    valueField: 'id',
    triggerAction: 'all',
    selectOnFocus: true,
    editable: false,
    pageSize: Toc.CONF.GRID_PAGE_SIZE,
    emptyText: 'Accessories',
    width: 400
  });
  
  config.tbar = [
    {
      text: TocLanguage.btnRefresh,
      iconCls: 'refresh',
      handler: this.onRefresh,
      scope: this
    }, 
    '->', 
    config.cboProducts,
    {
      text: 'Insert',
      iconCls : 'add',
      handler: this.addProduct,
      scope: this
    }
  ];
  
  Toc.products.AccessoriesPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.AccessoriesPanel, Ext.grid.GridPanel, {
  addProduct: function() {
    var accessoriesId = this.cboProducts.getValue();
    var productName = this.cboProducts.getRawValue().toString();

    if (!Ext.isEmpty(accessoriesId)) {
      store = this.getStore();
      
      if (store.findExact('accessories_id', accessoriesId) == -1) {
        var record = Ext.data.Record.create([
          {name: 'accessories_id', type: 'string'},
          {name: 'products_name', type: 'string'}
        ]);
        
        var v = new record({
          accessories_id: accessoriesId,
          products_name: productName
        });
        
        store.add(v);
      }
    }
  },

  onRowAction: function(grid, record, action, row, col) {
    switch(action) {
      case 'icon-delete-record':
        this.getStore().removeAt(row);
        break;
    }
  },
  
  onRefresh: function() {
    this.getStore().reload();
  },
  
  getAccessoriesIds: function() {
    var batch = [];
    
    this.getStore().each(function(record) {
      batch.push(record.get('accessories_id'));
    });
    
    return batch.join(';');
  }
});

Toc.products.VariantsGroupsDialog = function(config) {
  config = config || {};
  
  config.width = 450;
  config.height = 300;
  config.layout = 'fit';
  config.modal = true;
  config.id = 'variants_group-dialog-win';
  config.iconCls = 'icon-product_variants-win';
  config.title = 'Variants Groups';
  config.items = this.buildGrid();

  config.buttons = [{
    text: TocLanguage.btnAdd,
    handler: function() {
      this.submitForm();
    },
    scope: this
  }, {
    text: TocLanguage.btnClose,
    handler: function() { 
      this.close();
    },
    scope: this
  }];
  
  this.addEvents({'groupChange' :true});
  
  Toc.products.VariantsGroupsDialog.superclass.constructor.call(this, config);
}

Ext.extend(Toc.products.VariantsGroupsDialog, Ext.Window, {
  buildGrid: function() {
    var dsVariantGroups = new Ext.data.Store({
      url: Toc.CONF.CONN_URL,
      baseParams: {
        module: 'products',
        action: 'load_variants_groups'     
      },
      reader: new Ext.data.JsonReader({
        root: Toc.CONF.JSON_READER_ROOT,
        totalProperty: Toc.CONF.JSON_READER_TOTAL_PROPERTY,
        id: 'groups_id'
      },  [
        'groups_id',
        'groups_name'
      ]),
      autoLoad: true,
      listeners: {
        load: this.onDsVariantGroupsLoad,
        scope: this
      }
    });

    var sm = new Ext.grid.CheckboxSelectionModel();
    this.grdProductsVariants = new Ext.grid.GridPanel({
      viewConfig: {
        emptyText: TocLanguage.gridNoRecords
      },
      border: false,
      ds: dsVariantGroups,
      sm: sm,
      cm: new Ext.grid.ColumnModel([
        sm,
        {id: 'products_variants_groups_name', header: 'Name', dataIndex: 'groups_name'}
      ]),
      autoExpandColumn: 'products_variants_groups_name',
      tbar: [{
        text: TocLanguage.btnRefresh,
        iconCls: 'refresh',
        handler: this.onRefresh,
        scope: this
      }]
    });    
    
    return this.grdProductsVariants;
  },
  
  onDsVariantGroupsLoad: function() {
    var rows = [];
    
    Ext.each(this.group_ids, function(id){
      var row =  this.grdProductsVariants.store.findExact('groups_id', id);
      rows.push(row);
    }, this);
    
    this.grdProductsVariants.selModel.selectRows(rows);
  },
  
  onRefresh: function() {
    this.grdProductsVariants.getSotre().reload();
  },
  
  submitForm: function() {
    var groups = [];
    var records = this.grdProductsVariants.getSelectionModel().getSelections();
    
    Ext.each(records, function(record) {
      var group = {id: record.get('groups_id'), name: record.get('groups_name')};
      groups.push(group); 
    });
    
    if (groups.length > 0) {
      this.fireEvent('groupChange', groups);
    }

    this.close();
  }
});
Toc.products.CategoriesTreePanel = function(config) {
  config = config || {};
  
  config.region = 'west';
  config.border = false;
  config.autoScroll = true;
  config.containerScroll = true;
  config.split = true;
  config.width = 170;
  config.enableDD = true;
  config.ddGroup = 'productDD';
  config.rootVisible = true;
  
  config.root = new Ext.tree.AsyncTreeNode({
    text: '-- Top Category --',
    draggable: false,
    id: '0',
    expanded: true
  });
  config.currentCategoryId = '0';
    
  config.loader = new Ext.tree.TreeLoader({
    dataUrl: Toc.CONF.CONN_URL,
    preloadChildren: true, 
    baseParams: {
      module: 'categories',
      action: 'load_categories_tree'
    },
    listeners: {
      load: function() {
        this.expandAll();
        this.setCategoryId(0);
      },
      scope: this
    }
  });
  
  config.tbar = [{
    text: TocLanguage.btnRefresh,
    iconCls: 'refresh',
    handler: this.refresh,
    scope: this
  }];
  
  config.listeners = {
    "click": this.onCategoryNodeClick, 
    "nodedragover": this.onCategoryNodeDragOver,
    "nodedrop": this.onCategoryNodeDrop,
    "beforenodedrop": this.onBeforeNodeDrop,
    "contextmenu": this.onCategoryNodeRightClick
  };
  
  this.addEvents({'selectchange' : true});
  
  Toc.products.CategoriesTreePanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.CategoriesTreePanel, Ext.tree.TreePanel, {
  
  onBeforeNodeDrop: function(dropEvent) {
    var targetCategoriesId = dropEvent.target.id;
    var products = dropEvent.data.selections;
    
    if ( !Ext.isEmpty(products) ) {
      keys = [];
      for (i = 0; i < products.length; i++) {
        keys.push(products[i].id);
      }
   
      if(keys.length > 0) {
        this.body.mask(TocLanguage.loadingText);
        
        Ext.Ajax.request({
          url: Toc.CONF.CONN_URL,
          params: {
            module: 'products',
            action: 'move_products',
            target_categories_id: targetCategoriesId,
            old_categories_id: this.selectedNode.id,
            batch: keys.join(',')
          },
          callback: function(options, success, response) {
            this.body.unmask();
            result = Ext.decode(response.responseText);
            
            if (result.success == true) {
              var targetNode = this.getNodeById(targetCategoriesId);
              targetNode.select();
              this.fireEvent('selectchange', targetCategoriesId);
            }
          },
          scope: this
        }); 
      }
    }
  },
  
  setCategoryId: function(categoryId) {
    var currentNode = this.getNodeById(categoryId);
    currentNode.select();
    this.currentCategoryId = categoryId;
    this.selectedNode = currentNode;
    
    this.fireEvent('selectchange', categoryId);
  },
  
  onCategoryNodeClick: function (node) {
    node.expand();
    this.setCategoryId(node.id);
  },
  
  onCategoryNodeDragOver: function (e) {
    if (e.target.leaf == true) {
	    e.target.leaf = false;
	  }
	  
	  if (e.target.id == this.selectedNode.id) {
	    return false;
	  }
	  
	  return true;
  },
  
  onCategoryNodeDrop: function(e) {
    if (e.point == 'append') {
      parent_id = e.target.id;
      currentCategoryId = e.target.id;    
    } else {
      parent_id = e.target.parentNode.id;
      currentCategoryId = e.target.parentNode.id;
    }
    
    Ext.Ajax.request ({
      url: Toc.CONF.CONN_URL,
      params: {
        module: 'categories',
        action: 'move_categories',
        categories_ids: e.dropNode.id,
        parent_category_id: parent_id
      },
      callback: function(options, success, response){
        result = Ext.decode(response.responseText);
        
        if (result.success == true) {
          this.setCategoryId(currentCategoryId);
        } else {
          Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
        }
      },
      scope: this
    });
  },
  
  getCategoriesPath: function(node) {
    var cpath = [];
    node = (node == null) ? this.getNodeById(this.currentCategoryId) : node;
    
    while (node.id > 0) {
      cpath.push(node.id);
      node = node.parentNode;
    }
    
    return cpath.reverse().join('_');
  },
  
  onCategoryNodeRightClick: function(node, event) {
    event.preventDefault();
    node.select();
    
    this.menuContext = new Ext.menu.Menu({
      items: [
        {
          text: TocLanguage.btnAdd,
          iconCls: 'add',
          handler: function() {
            var path = this.getCategoriesPath(node);
            var root = this.root;
            
            TocDesktop.callModuleFunc('categories', 'createCategoriesDialog', function(dlg){
              dlg.on('saveSuccess', function(feedback, categoriesId, text) {
                node.appendChild({
                  id: categoriesId, 
                  text: text, 
                  cls: 'x-tree-node-collapsed', 
                  parent_id: node.id, 
                  leaf: true
                });
                
                node.expand();
              }, this);
              
              dlg.show(null, path);
            });
          },
          scope: this
        },
        {
          text: TocLanguage.tipEdit,
          iconCls: 'edit',
          handler: function() {
            var path = this.getCategoriesPath(node);
            var root = this.root;
            
            TocDesktop.callModuleFunc('categories', 'createCategoriesDialog', function(dlg){
              dlg.on('saveSuccess', function(feedback, categoriesId, text) {
                node.setText(text);
              }, this);
              
              dlg.show(node.id, path);
            });
          },
          scope: this
        },
        {
          text: TocLanguage.tipDelete,
          iconCls: 'remove',
          handler:  function() {
            Ext.MessageBox.confirm(
              TocLanguage.msgWarningTitle, 
              TocLanguage.msgDeleteConfirm, 
              function (btn) {
                if (btn == 'yes') {
                  currentCategoryId = node.parentNode.id;
                  
                  Ext.Ajax.request({
                    url: Toc.CONF.CONN_URL,
                    params: {
                      module: 'categories',
                      action: 'delete_category',
                      categories_id: node.id
                    },
                    callback: function (options, success, response) {
                      var result = Ext.decode(response.responseText);
                      
                      if (result.success == true) {
                        var pNode = node.parentNode;
                        pNode.ui.addClass('x-tree-node-collapsed');
                        
                        node.remove();
                        this.setCategoryId(currentCategoryId);
                      } else {
                        Ext.MessageBox.alert(TocLanguage.msgErrTitle, result.feedback);
                      }
                    },
                    scope: this
                  });
                }
              }, 
              this
            );
          },
          scope: this
        }
      ]
    });
    
    this.menuContext.showAt(event.getXY());;
  },
  
  refresh: function() {
    this.root.reload();
  }
});Toc.products.ProductsMainPanel = function(config) {
  config = config || {};
  
  config.layout = 'border';
  config.border = false;

  config.pnlCategoriesTree = new Toc.products.CategoriesTreePanel({owner: config.owner, parent: this});
  config.grdProducts = new Toc.products.ProductsGrid({owner: config.owner, mainPanel: this});
  
  config.pnlCategoriesTree.on('selectchange', this.onPnlCategoriesTreeNodeSelectChange, this);
  
  config.items = [config.pnlCategoriesTree, config.grdProducts];
  
  Toc.products.ProductsMainPanel.superclass.constructor.call(this, config);
};

Ext.extend(Toc.products.ProductsMainPanel, Ext.Panel, {
  
  onPnlCategoriesTreeNodeSelectChange: function(categoryId) {
    this.grdProducts.refreshGrid(categoryId);
  },
  
  getCategoriesTree: function() {
    return this.pnlCategoriesTree;
  }
});

Ext.override(TocDesktop.ProductsWindow, {

  createWindow : function(){
    switch(this.id) {
      case 'products-dialog-win':
        win = this.createProductDialog();
        break;
      case 'products-win':
        win = this.createProductsWindow();
        break;
      case 'products_attachments-win':
        win = this.createProductsAttachmentsWindow();
        break;
    }
    win.show();
  },

  createProductsWindow: function(productId) {
    var desktop = this.app.getDesktop();
    win = desktop.getWindow('products-win');

    if(!win){
      pnl = new Toc.products.ProductsMainPanel({owner: this});

      win = desktop.createWindow({
        id: 'products-win',
        title:'Products',
        width:870,
        height:400,
        iconCls: 'icon-products-win',
        layout: 'fit',
        items: pnl
      });
    }

    return win;
  },

  createProductDialog: function(productId) {
    var desktop = this.app.getDesktop();
    var dlg = desktop.getWindow('products-dialog-win');
    
    if (!dlg) {
      dlg = desktop.createWindow({products_id: productId, owner: this}, Toc.products.ProductDialog);
    }
        
    return dlg;
  },
  
  createProductDuplicateDialog: function(productsId) {
    var desktop = this.app.getDesktop();
    var dlg = desktop.getWindow('products_duplicate-dialog-win');
    
    if (!dlg) {
      dlg = desktop.createWindow({productsId: productsId, owner: this}, Toc.products.ProductsDuplicateDialog);
      
      dlg.on('saveSuccess', function (feedback) {
        this.app.showNotification({
          title: TocLanguage.msgSuccessTitle,
          html: feedback
        });
      }, this);
    }
        
    return dlg;
  },
  
  createProductsAttachmentsWindow: function() {
    var desktop = this.app.getDesktop();
    var win = desktop.getWindow('products_attachments-win');
     
    if (!win) {
      grd = new Toc.products.AttachmentsGrid({owner: this});
      
      win = desktop.createWindow({
        id: 'products_attachments-win',
        title: 'Attachments',
        width: 800,
        height: 400,
        iconCls: 'icon-products_attachments-win',
        layout: 'fit',
        items: grd
      });
    }
    
    return win;
  },
  
  createAttachmentsListDialog: function(productsId) {
    var desktop = this.app.getDesktop();
    var dlg = desktop.getWindow('products_attachments_list_dialog-win');
    
    if (!dlg) {
      dlg = desktop.createWindow({productsId: productsId}, Toc.products.AttachmentsListDialog);
    }
        
    return dlg;
  },
  
  createAttachmentsDialog: function() {
    var desktop = this.app.getDesktop();
    var dlg = desktop.getWindow('products_attachments_dialog-win');
    
    if (!dlg) {
      dlg = desktop.createWindow({}, Toc.products.AttachmentsDialog);
      
      dlg.on('saveSuccess', function (feedback) {
        this.app.showNotification({
          title: TocLanguage.msgSuccessTitle,
          html: feedback
        });
      }, this);
    }
    return dlg;
  },
  
  createCategoryMoveDialog: function(productId) {
    var desktop = this.app.getDesktop();
    var dlg = desktop.getWindow('products-move-dialog-win');
    
    if (!dlg) {
      dlg = desktop.createWindow({}, Toc.products.CategoriesMoveDialog);
      
      dlg.on('saveSuccess', function (feedback) {
        this.app.showNotification({
          title: TocLanguage.msgSuccessTitle,
          html: feedback
        });
      }, this);
    }
    
    return dlg;
  },
  
  createCustomizationsDialog: function(config) {
    var desktop = this.app.getDesktop();
    var dlg = desktop.getWindow('customization_fields_dialog-win');
    
    if (!dlg) {
      dlg = desktop.createWindow(config, Toc.products.CustomizationsDialog);
    }
    return dlg;
  },
  
  createVariantsGroupDialog: function(group_ids) {
    var desktop = this.app.getDesktop();
    var dlg = desktop.getWindow('variants_group-dialog-win');
    
    if (!dlg) {
      dlg = desktop.createWindow({owner: this, group_ids: group_ids}, Toc.products.VariantsGroupsDialog);
    }
    
    return dlg;
  }
});
