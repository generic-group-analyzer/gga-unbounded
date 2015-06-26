/// <reference path="zoocrypt.ts" />
/* ******************************************************************/
/* webSocket event loop                                             */
/* ******************************************************************/
webSocket.onmessage = function (evt) {
    log(evt.data);
    console.log(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n");
    var m = JSON.parse(evt.data);
    // answer for eval
    if (m.cmd == 'setGoal') {
        var dbg = m.debug;
        if (dbg != "") {
            console.log(dbg);
        }
        setFirstUnlocked(m.ok_upto);
        markLocked('locked');
        setGoalHtml("$\alpha = \omega$" + m.arg);
        if (m.err) {
            setMessageHtml(m.err);
        }
        else {
            var msg = m.msgs.length > 0 ? m.msgs[m.msgs.length - 1] : "No message received.";
            setMessageHtml(msg);
        }
    }
    else if (m.cmd == 'setDebug') {
        setMessageHtml(m.arg);
    }
    else if (m.cmd == 'setFiles') {
        files = (m.arg);
        renderOpenDialog(files);
    }
    else if (m.cmd == 'setProof') {
        currentFile = m.filename;
        renderToolbar(currentFile);
        editorProof.setValue(m.arg);
        editorProof.clearSelection();
        editorProof.scrollPageUp();
        setMessageHtml("Proofscript loaded.");
        var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
        editorProof.moveCursorToPosition(pos);
    }
    else if (m.cmd == "saveOK") {
        setMessageHtml("Proofscript saved.");
    }
    else if (m.cmd == "saveFAILED") {
        setMessageHtml("Save of proofscript failed.");
    }
};
