/** @jsx React.DOM */

var reportStyle = {
  overflowY: 'scroll', backgroundColor: 'white',
  color: 'black'
}

/* TEXOUT: This is the layout of the editor buffers, there are three
   divs for the proof editor, the goal, and the error messages. */
var Editors = React.createClass({displayName: "Editors",
  render: function() {
    return (
      React.createElement("div", {className: "row"}, 
        React.createElement("div", {className: "col-md-12"}, 
          React.createElement("table", null, 
            React.createElement("tbody", null, 
              React.createElement("tr", null, 
                React.createElement("td", null, 
                  React.createElement("div", {className: "editor", id: "editor-proof"})
                ), 
                React.createElement("td", null, 
                  React.createElement("div", {className: "editor", style: reportStyle, 
                       id: "editor-goal"}), 
                  React.createElement("div", {className: "editor", style: reportStyle, 
                       id: "editor-message"})
                )
              )
            )
          )
        )
      ))
  }
});

function renderEditors() {
  React.render(
      React.createElement(Editors, null)
    , document.getElementById('content')
  );
}


renderEditors();
