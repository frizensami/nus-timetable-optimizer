import React, { useState, useEffect } from 'react'

import { TimetableOutput } from '../core/timetable_to_smtlib2'
import { Segment, Button, Container, Divider } from 'semantic-ui-react'
import { GenericTimetable } from '../core/generic_timetable'
import { Z3Manager, Z3Callbacks } from '../core/z3_manager'
import { NUSModsFrontend } from '../frontends/nusmods_frontend'
import './Solver.css'


export const Solver: React.FC<{onNewTimetable(timetable: any): any}> = ({onNewTimetable}) => {

    let [smtlibInput, setSmtlibInput] = useState<String>("");
    let [smtlibOutput, setSmtlibOutput] = useState<String>("");

    function onZ3Initialized() {
        Z3Manager.solve()
    }

    function updateInputSmtlib2(smtStr: string) {
        setSmtlibInput(smtStr)
    }

    function onOutput(smtStr: string) {
        setSmtlibOutput(smtStr)
    }

    function onTimetableOutput(timetable: TimetableOutput) {
        // setSmtlibOutput(smtStr)
        console.log(timetable)
        onNewTimetable(timetable);
    }

    const callbacks: Z3Callbacks = {
        onZ3Initialized: onZ3Initialized,
        onSmtlib2InputCreated: updateInputSmtlib2,
        onOutput: onOutput,
        onTimetableOutput: onTimetableOutput
    }

    function onSubmit() {
        console.log("Initializing z3 worker");
        // console.log(worker)
        let nusmods_fe = new NUSModsFrontend();
        nusmods_fe.add_module("CS3203", "2020-2021", 1, true).then(() => {
            console.log(nusmods_fe);
            const gt: GenericTimetable = nusmods_fe.create_timetable(5, 10);
            Z3Manager.init(gt, callbacks);
            Z3Manager.initZ3();
        });

    }


    return (
        <div className="solver">

            <Container>
                <Segment raised>
                    <h3 className="ui center aligned header"> Modules & Constraints </h3>
                    <Button onClick={onSubmit} attached="bottom">Run Solver</Button>
                </Segment>
            </Container>

            <Divider />

            <Container>
                <Segment raised inverted style={{ overflow: 'auto', maxHeight: 200 }}>
                    <h3 className="ui center aligned header"> SMTLIB2 Input </h3>
                    <div className="display-linebreak">
                        {smtlibInput.replace(/ /g, "\u00a0")}
                    </div>
                </Segment>
            </Container>


            <Divider />

            <Container>
                <Segment raised inverted color="grey" style={{ overflow: 'auto', maxHeight: 200 }}>
                    <h3 className="ui center aligned header"> SMTLIB2 Output </h3>
                    <div className="display-linebreak">
                        {smtlibOutput.replace(/ /g, "\u00a0")}
                    </div>
                </Segment>
            </Container>
        </div>
    );
}
