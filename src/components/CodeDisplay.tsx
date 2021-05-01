import React, { useState, useEffect } from 'react'
import './Solver.css'
import { Segment, Button, Container, Divider } from 'semantic-ui-react'

export const CodeDisplay: React.FC<{ code: string, color: string, headerText: string }> = ({ code, color, headerText }) => {

    return (

        <Segment raised inverted color={color as any}>
            <h3 className="ui center aligned header"> {headerText}</h3>
            <Divider />
            <Segment raised inverted color={color as any} style={{ overflow: 'auto', maxHeight: 200 }}>
                <div className="display-linebreak">
                    {code.replace(/ /g, "\u00a0")}
                </div>
            </Segment>
        </Segment>
    )
}
