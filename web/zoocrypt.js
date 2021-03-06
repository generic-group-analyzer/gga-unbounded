/// <reference path="typedefs/ace.d.ts" />
/// <reference path="typedefs/jquery.d.ts" />
/// <reference path="typedefs/mathjax.d.ts" />
/// <reference path="typedefs/showdown.d.ts" />
/* ******************************************************************/
/* Debug logging                                                    */
/* ******************************************************************/
var enable_debug = false;
function log(s) {
    if (enable_debug) {
        console.log(s);
    }
}
/* ******************************************************************/
/* Websocket connection                                             */
/* ******************************************************************/
var wsServer = window.location.hostname ? window.location.hostname : "127.0.0.1";
var webSocket = new ReconnectingWebSocket("ws://" + wsServer + ":9999/");
var firstConnect = true;
var files = [];
var currentFile = "";
//webSocket.onclose = function(evt) {
//  log("reconnecting to server");
//  webSocket = new WebSocket("ws://" + wsServer + ":9999/");
//};
// send json request to zoocrypt websocket server
function sendZoocrypt(m) {
    if (webSocket) {
        webSocket.send(JSON.stringify(m));
    }
}
/* ******************************************************************/
/* Locking in proof editor                                          */
/* ******************************************************************/
// editorProof has been processed up to this character
var firstUnlocked = 0;
// the text from the timepoint when the locking was enabled
var originalLockedText = "";
// the last locking marker, used for removal
var lastMarker;
function lockedText() {
    return editorProof.getValue().substring(0, firstUnlocked);
}
function setFirstUnlocked(i) {
    firstUnlocked = i;
    originalLockedText = lockedText();
}
function insideCommentOrString(t, pos) {
    var i = 0;
    var insideComment = false;
    var insideString = false;
    while (i < pos) {
        if (insideComment) {
            if (t[i] == "*" && t.length > i + 1 && t[i + 1] == ")") {
                insideComment = false;
            }
        }
        else if (insideString) {
            if (t[i] == "\"") {
                insideString = false;
            }
        }
        else {
            if (t[i] == "(" && t.length > i + 1 && t[i + 1] == "*") {
                insideComment = true;
            }
            else if (t[i] == "\"") {
                insideString = true;
            }
        }
        i++;
    }
    return insideComment || insideString;
}
function getNextDot(from) {
    var t = editorProof.getValue();
    var n = t.indexOf(".", from);
    if (n !== -1 && insideCommentOrString(t, n)) {
        return getNextDot(n + 1);
    }
    return n;
}
function getPrevDot(from) {
    var t = editorProof.getValue();
    var n = t.lastIndexOf(".", Math.max(0, from - 2));
    if (n !== -1 && insideCommentOrString(t, n)) {
        return getPrevDot(n - 1);
    }
    return n;
}
var emacs = ace.require("ace/keyboard/emacs").handler;
var editorProof = ace.edit("editor-proof");
editorProof.setTheme("ace/theme/eclipse");
editorProof.setShowPrintMargin(false);
editorProof.setDisplayIndentGuides(false);
editorProof.setHighlightActiveLine(false);
editorProof.focus();
editorProof.renderer.setShowGutter(false);
editorProof.setKeyboardHandler(emacs);
editorProof.getSession().setTabSize(2);
editorProof.getSession().setUseSoftTabs(true);
editorProof.getSession().setMode("ace/mode/zoocrypt");
editorProof.getSession().getDocument().on("change", function (ev) {
    var lt = lockedText();
    if (lt !== originalLockedText) {
        // search for the last dot that is the common prefix of
        // old and new content of locked region
        var lastDot = 0;
        for (var i = 0; i < Math.min(lt.length, originalLockedText.length); i++) {
            if (lt.charAt(i) !== originalLockedText.charAt(i)) {
                break;
            }
            if (lt.charAt(i) == '.' && !insideCommentOrString(lt, i)) {
                lastDot = i;
            }
        }
        var pos = editorProof.getCursorPosition();
        setFirstUnlocked(lastDot + 1);
        evalLocked();
        editorProof.moveCursorToPosition(pos);
    }
});
function markLocked(c) {
    var Range = ace.require('ace/range').Range;
    var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
    if (lastMarker) {
        editorProof.getSession().removeMarker(lastMarker);
    }
    lastMarker = editorProof.getSession().addMarker(new Range(0, 0, pos.row, pos.column), c, 'word', false);
}
/* ******************************************************************/
/* Goal and message editor and resizing                             */
/* ******************************************************************/
/* TEXOUT: We create an ACE editor instance here and attach it to the
     div "editor-goal".
     If we comment this out, there will just be a div and we can directly
     write content into the div. */
// var editorGoal = ace.edit("editor-goal");
// editorGoal.setTheme("ace/theme/eclipse");
// editorGoal.setHighlightActiveLine(false);
// editorGoal.setShowPrintMargin(false);
// editorGoal.setDisplayIndentGuides(false);
// editorGoal.renderer.setShowGutter(false)
function setGoalHtml(s) {
    // we use <script ..> .. </script> instead of $..$ or $$..$$ to ensure
    // that showdown does not touch our formulas.
    // var markdown =
    //  "# Nice output\n" +
    //  "\n"+
    //  '1. <p><script type="math/tex" mode="display">foo = \\alpha + \\beta</script></p>\n' +
    //  "\n"+
    //  '2. <p><script type="math/tex" mode="display">bar = \\sum_{i=0}^{k} a_i + \\forall j. j = i</script></p>\n' +
    //  "\n" +
    //  "## Old output\n"; 
    //var html = converter.makeHtml(markdown);
    var converter = new showdown.Converter();
    var latex = converter.makeHtml(s);
    document.getElementById('editor-goal').innerHTML = latex;
    // translate mathjax content
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, 'editor-goal']);
}
function setMessageHtml(s) {
    document.getElementById('editor-message').innerHTML = "<pre>" + s + "</pre>";
    // translate mathjax content
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, 'editor-message']);
}
// var editorMessage = ace.edit("editor-message");
// editorMessage.setTheme("ace/theme/eclipse");
// editorMessage.setHighlightActiveLine(false);
// editorMessage.setDisplayIndentGuides(false);
// editorMessage.setShowPrintMargin(false);
// editorMessage.renderer.setShowGutter(false);
// resize windows
function resizeAce() {
    var hpadding = 40;
    var vpadding = 100;
    var edit = $('#editor-proof');
    edit.height($(window).height() - vpadding + 13);
    edit.width($(window).width() / 3 - hpadding);
    edit = $('#editor-goal');
    edit.height(($(window).height() - vpadding) * 0.8);
    edit.width($(window).width() * 2 / 3 - hpadding);
    edit = $('#editor-message');
    edit.height(($(window).height() - vpadding) * 0.2);
    edit.width($(window).width() * 2 / 3 - hpadding);
}
//listen for changes
$(window).resize(resizeAce);
//set initially
resizeAce();
/* ******************************************************************/
/* File handling functions                                         */
/* ******************************************************************/
function saveBuffer() {
    sendZoocrypt({ 'cmd': 'save', 'arg': editorProof.getValue(), 'filename': currentFile });
}
function loadBuffer(fname) {
    sendZoocrypt({ 'cmd': 'load', 'arg': fname });
}
function getDebug() {
    sendZoocrypt({ 'cmd': 'getDebug', 'arg': '' });
}
/* ******************************************************************/
/* Websocket event handling                                         */
/* ******************************************************************/
// Request proof script
webSocket.onopen = function (evt) {
    if (firstConnect) {
        sendZoocrypt({ 'cmd': 'load', 'arg': '' });
        sendZoocrypt({ 'cmd': 'listFiles', 'arg': '' });
    }
    firstConnect = false;
};
/* ******************************************************************/
/* Evaluate parts of buffer                                         */
/* ******************************************************************/
function evalLocked() {
    var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
    editorProof.moveCursorToPosition(pos);
    editorProof.clearSelection();
    markLocked('processing');
    if (lockedText() !== "") {
        sendZoocrypt({ 'cmd': 'eval', 'arg': lockedText(), 'filename': currentFile });
    }
    else {
        setGoalHtml("");
        setMessageHtml("");
    }
}
function evalNext() {
    var nextDot = getNextDot(firstUnlocked);
    if (nextDot > firstUnlocked) {
        setFirstUnlocked(nextDot + 1);
        evalLocked();
    }
}
function evalCursor() {
    var pos = editorProof.getCursorPosition();
    var idx = editorProof.getSession().getDocument().positionToIndex(pos, 0);
    var prevDot = getPrevDot(idx + 1);
    if (prevDot == -1) {
        setFirstUnlocked(0);
    }
    else {
        setFirstUnlocked(prevDot + 1);
    }
    evalLocked();
}
function evalPrev() {
    var prevDot = getPrevDot(firstUnlocked);
    if (prevDot == -1) {
        setFirstUnlocked(0);
    }
    else {
        setFirstUnlocked(prevDot + 1);
    }
    evalLocked();
}
/* ******************************************************************/
/* Add command bindings buffer                                      */
/* ******************************************************************/
editorProof.commands.addCommand({
    name: 'saveFile',
    bindKey: {
        win: 'Ctrl-S',
        mac: 'Command-S',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        saveBuffer();
    }
});
editorProof.commands.addCommand({
    name: 'getDebugFile',
    bindKey: {
        win: 'Ctrl-D',
        mac: 'Command-D',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        getDebug();
    }
});
editorProof.commands.addCommand({
    name: 'evalCursor',
    bindKey: {
        win: 'Ctrl-Enter',
        mac: 'Ctrl-Enter',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        evalCursor();
    }
});
editorProof.commands.addCommand({
    name: 'evalNext',
    bindKey: {
        win: 'Ctrl-n',
        mac: 'Ctrl-n',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        evalNext();
    }
});
editorProof.commands.addCommand({
    name: 'evalPrev',
    bindKey: {
        win: 'Ctrl-p',
        mac: 'Ctrl-p',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        evalPrev();
    }
});
