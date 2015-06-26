/** @jsx React.DOM */

var reportStyle = {
  overflowY: 'scroll', backgroundColor: 'white',
  color: 'black'
}

/* TEXOUT: This is the layout of the editor buffers, there are three
   divs for the proof editor, the goal, and the error messages. */
var Editors = React.createClass({
  render: function() {
    return (
      <div className="row">
        <div className="col-md-12">
          <table>
            <tbody>
              <tr>
                <td>
                  <div className="editor" id="editor-proof"></div>
                </td>
                <td>
                  <div className="editor" style={reportStyle}
                       id="editor-goal"></div>
                  <div className="editor" style={reportStyle}
                       id="editor-message"></div>
                </td>
              </tr>
            </tbody>
          </table>
        </div>
      </div>)
  }
});

function renderEditors() {
  React.render(
      <Editors/>
    , document.getElementById('content')
  );
}


renderEditors();
