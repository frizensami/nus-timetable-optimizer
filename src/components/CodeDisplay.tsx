import React, { useState, useEffect } from 'react';
import './Solver.css';
import { Segment, Button, Container, Divider } from 'semantic-ui-react';

import AceEditor from 'react-ace';
import 'ace-builds/src-noconflict/mode-python';
import 'ace-builds/src-noconflict/theme-monokai';
import 'ace-builds/src-noconflict/theme-tomorrow';

const CodeDisplay: React.FC<{
    code: string;
    theme: string;
    headerText: string;
}> = ({ code, theme, headerText }) => {
    // <Segment raised inverted color={color as any} style={{ overflow: 'auto', maxHeight: 200 }}>
    //     <div className="display-linebreak">
    //         {code.replace(/ /g, "\u00a0")}
    //     </div>
    // </Segment>

    return (
        <Segment raised inverted={theme == 'dark'}>
            <h3 className="ui center aligned header"> {headerText}</h3>
            <Divider />
            <AceEditor
                mode="python"
                theme={theme == 'dark' ? 'monokai' : 'tomorrow'}
                value={code}
                setOptions={{
                    readOnly: true,
                    fontSize: 18,
                }}
                style={{ width: '100%' }}
            />
        </Segment>
    );
};

export default CodeDisplay;
