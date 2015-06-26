/// <reference path="ace.d.ts" />
/// <reference path="jquery.d.ts" />
/// <reference path="mathjax.d.ts" />
var enable_debug = false;
function log(s) {
    if (enable_debug) {
        console.log(s);
    }
}
var wsServer = window.location.hostname ? window.location.hostname : "127.0.0.1";
var webSocket = new ReconnectingWebSocket("ws://" + wsServer + ":9999/");
var firstConnect = true;
var files = [];
var currentFile = "";
function sendZoocrypt(m) {
    if (webSocket) {
        webSocket.send(JSON.stringify(m));
    }
}
var firstUnlocked = 0;
var originalLockedText = "";
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
function setGoalHtml(s) {
    document.getElementById('editor-goal').innerHTML = "<p>\\(\\alpha = \\omega\\)</p><pre>" + s + "</pre>";
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, 'editor-goal']);
}
function setMessageHtml(s) {
    document.getElementById('editor-message').innerHTML = "<pre>" + s + "</pre>";
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, 'editor-message']);
}
function resizeAce() {
    var hpadding = 40;
    var vpadding = 100;
    var edit = $('#editor-proof');
    edit.height($(window).height() - vpadding + 13);
    edit.width($(window).width() / 2 - hpadding);
    edit = $('#editor-goal');
    edit.height(($(window).height() - vpadding) * 0.6);
    edit.width($(window).width() / 2 - hpadding);
    edit = $('#editor-message');
    edit.height(($(window).height() - vpadding) * 0.4);
    edit.width($(window).width() / 2 - hpadding);
}
$(window).resize(resizeAce);
resizeAce();
function saveBuffer() {
    sendZoocrypt({ 'cmd': 'save', 'arg': editorProof.getValue(), 'filename': currentFile });
}
function loadBuffer(fname) {
    sendZoocrypt({ 'cmd': 'load', 'arg': fname });
}
function getDebug() {
    sendZoocrypt({ 'cmd': 'getDebug', 'arg': '' });
}
webSocket.onopen = function (evt) {
    if (firstConnect) {
        sendZoocrypt({ 'cmd': 'load', 'arg': '' });
        sendZoocrypt({ 'cmd': 'listFiles', 'arg': '' });
    }
    firstConnect = false;
};
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
