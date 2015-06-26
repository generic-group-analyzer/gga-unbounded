/** @jsx React.DOM */

var goalStyle = { overflowY: 'scroll', backgroundColor: 'white' }

/* TEXOUT: This is the layout of the editor buffers, there are three
   divs for the proof editor, the goal, and the error messages. */
var Editors = React.createClass({displayName: 'Editors',
  render: function() {
    return (
      React.DOM.div({className: "row"}, 
        React.DOM.div({className: "col-md-12"}, 
          React.DOM.table(null, 
            React.DOM.tbody(null, 
              React.DOM.tr(null, 
                React.DOM.td(null, 
                  React.DOM.div({className: "editor", id: "editor-proof"})
                ), 
                React.DOM.td(null, 
                  React.DOM.div({className: "editor", style: goalStyle, 
                       id: "editor-goal"}), 
                  React.DOM.div({className: "editor", 
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
  React.renderComponent(
      Editors(null)
    , document.getElementById('content')
  );
}


renderEditors();
