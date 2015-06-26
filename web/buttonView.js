/** @jsx React.DOM */

/* ******************************************************************/
/* Open Dialog                                                      */
/* ******************************************************************/

var FileButton = React.createClass({displayName: "FileButton",
  render: function() {
    var file = this.props.file;
    var closeDialog = this.props.closeDialog;
    var hclick = function () {
      loadBuffer(file);
      closeDialog();
    };
    return React.createElement("button", {type: "button", className: "btn btn-default", style: {textAlign: "left"}, onClick: hclick}, file);
  }
});

var FileButtons = React.createClass({displayName: "FileButtons",
 render: function() {
     var closeDialog = this.props.closeDialog;
     var files = this.props.files;
     return (
      React.createElement("div", {className: "btn-group-vertical", style: {paddingBottom: "10px"}}, 
         files.map(function (fn) { return React.createElement(FileButton, {key: fn, file: fn, closeDialog: closeDialog}) })
      ));extr
 }
});

var OpenDialog = React.createClass({displayName: "OpenDialog",
 render: function() {
   var files = this.props.files;
   var closeDialog = (function(_this) {
     return (
       function() {
         $(_this.getDOMNode()).modal("hide");
       })
   })(this);
   
   return (
     React.createElement("div", {id: "open-file-modal", className: "modal"}, 
       React.createElement("div", {className: "modal-dialog"}, 
         React.createElement("div", {className: "modal-content"}, 
           React.createElement("div", {className: "modal-header", style: {textAlign: "center"}}, 
             React.createElement("h3", {className: "modal-title"}, "Open file")
           ), 
           React.createElement("div", {className: "modal-body", style: {textAlign: "center"}}, 
             React.createElement(FileButtons, {files: files, closeDialog: closeDialog})
           ), 
           React.createElement("div", {className: "modal-footer"}, 
             React.createElement("div", {className: "btn-group"}, 
               React.createElement("button", {type: "button", className: "btn btn-primary btn-default", 
                  onClick: closeDialog}, "Cancel")
             )
           )
         )
       )
     ));
 }
});

function renderOpenDialog(files) {
  React.render(
    React.createElement(OpenDialog, {files: files})
  , document.getElementById('open-dialog')
  );
}

renderOpenDialog(["no files available"]);

var NewDialog = React.createClass({displayName: "NewDialog",
  getInitialState: function() {
    return {filename: 'test.zc'};
  },

  handleChange: function(event) {
    this.setState({filename: event.target.value});
  },

 render: function() {
   var closeDialog = (function(_this) {
     return (
       function() {
         $(_this.getDOMNode()).modal("hide");
       })
   })(this);

   var openFile = (function(_this) {
     return (
       function() {
         loadBuffer(_this.state.filename);
         closeDialog();
       })
   })(this);

   var filename = this.state.filename;
   return (
     React.createElement("div", {id: "new-file-modal", className: "modal"}, 
       React.createElement("div", {className: "modal-dialog"}, 
         React.createElement("div", {className: "modal-content"}, 
           React.createElement("div", {className: "modal-header", style: {textAlign: "center"}}, 
             React.createElement("h3", {className: "modal-title"}, "Visit New File")
           ), 
           React.createElement("div", {className: "modal-body", style: {textAlign: "center"}}, 
              React.createElement("input", {type: "test", value: filename, onChange: this.handleChange})
           ), 
           React.createElement("div", {className: "modal-footer"}, 
             React.createElement("div", {className: "btn-group"}, 
               React.createElement("button", {type: "button", className: "btn btn-primary btn-default", 
                  onClick: closeDialog}, "Cancel"), 
               React.createElement("button", {type: "button", className: "btn btn-primary btn-default", 
                  onClick: openFile}, "Open")
             )
           )
         )
       )
     ));
 }
});

function renderNewDialog() {
  React.render(
    React.createElement(NewDialog, null)
  , document.getElementById('new-dialog')
  );
}

renderNewDialog();

/* ******************************************************************/
/* Toolbar                                                          */
/* ******************************************************************/

var Toolbar = React.createClass({displayName: "Toolbar",
  getInitialState: function() {
    // this is static and does not change
    return { ctrl: navigator.appVersion.indexOf('Mac') != -1 ? "Cmd" : "Ctrl" }
  },
  render: function() {

    var fn = this.props.curFile;

    var ctrl = this.state.ctrl;

    var openDialog = function() {
      $("#open-file-modal").modal('show');
    };

    var newDialog = function() {
      $("#new-file-modal").modal('show');
    };

    return (
      React.createElement("div", {className: "btn-toolbar"}, 
        React.createElement("button", {className: "btn btn-primary btn-default", onClick: openDialog}, "Open file"), 
        React.createElement("button", {className: "btn btn-primary btn-default", onClick: newDialog}, "New file"), 
        React.createElement("button", {className: "btn btn-primary btn-default", onClick: saveBuffer}, "Save (", ctrl, "-s)"), 
        React.createElement("button", {className: "btn btn-primary btn-default", onClick: evalNext}, "Eval next (Ctrl-n)"), 
        React.createElement("button", {className: "btn btn-primary btn-default", onClick: evalCursor}, "Eval up to cursor (Ctrl-return)"), 
        React.createElement("button", {className: "btn btn-primary btn-default", onClick: evalPrev}, "Undo eval (Ctrl-p)"), 
        React.createElement("span", {style: {paddingLeft: "10px"}}, "Editing ", fn==""?"<none>":fn)
      ));
  }});

function renderToolbar(fn) {
  React.render(
    React.createElement(Toolbar, {curFile: fn})
    , document.getElementById('toolbar-buttons')
  );
}

renderToolbar("");
