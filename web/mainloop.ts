/// <reference path="zoocrypt.ts" />

declare var renderToolbar
declare var renderOpenDialog

/* ******************************************************************/
/* webSocket event loop                                             */
/* ******************************************************************/

webSocket.onmessage = function (evt) {
  log(evt.data);
  console.log(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n");
  var m : Reply = JSON.parse(evt.data);

  // answer for eval
  if (m.cmd == 'setGoal') {
    var dbg = (<any>m).debug;
    if (dbg != "") { console.log(dbg); }
    setFirstUnlocked(m.ok_upto);
    markLocked('locked');
    setGoalHtml(m.arg);
    if (m.err) {
      setMessageHtml(m.err);
    } else {
      var msg = m.msgs.length > 0 ? m.msgs[m.msgs.length - 1] : "No message received.";
      setMessageHtml(msg);
    }

  // answer for get_debug
  } else if (m.cmd == 'setDebug') {
    setMessageHtml(m.arg);
    
  // answer for list files
  } else if (m.cmd == 'setFiles') {
    files = <any>(m.arg);
    renderOpenDialog(files);

  // answer for load
  } else if (m.cmd == 'setProof') {
    currentFile = (<any>m).filename;
    renderToolbar(currentFile);
    editorProof.setValue(m.arg);
    editorProof.clearSelection();
    editorProof.scrollPageUp();
    setMessageHtml("Proofscript loaded.");
    var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked,0);
    editorProof.moveCursorToPosition(pos);

  // answers for save
  } else if (m.cmd == "saveOK") {
    setMessageHtml("Proofscript saved.");

  // answers for failed save
  } else if (m.cmd == "saveFAILED") {
    setMessageHtml("Save of proofscript failed.");
  }
};
