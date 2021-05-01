import React, { useState, useEffect } from 'react'

import { TimetableOutput } from '../core/timetable_to_smtlib2'
import { Segment, Button, Container, Divider, Grid } from 'semantic-ui-react'
import { GenericTimetable } from '../core/generic_timetable'
import { Z3Manager, Z3Callbacks } from '../core/z3_manager'
import { NUSModsFrontend } from '../frontends/nusmods_frontend'
import { CodeDisplay } from './CodeDisplay'
import { ModuleConstraints } from './ModuleConstraints'
import { GlobalConstraints } from './GlobalConstraints'
import './Solver.css'


export const Solver: React.FC<{ onNewTimetable(timetable: any): any }> = ({ onNewTimetable }) => {

    let [smtlibInput, setSmtlibInput] = useState<string>("No input yet.");
    let [smtlibOutput, setSmtlibOutput] = useState<string>("No output yet.");

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
        let mod1 = {
            module_code: "CS3203",
            acad_year: "2020-2021",
            semester: 1,
            is_compulsory: true
        }
        let mod2 = {
            module_code: "CS2106",
            acad_year: "2020-2021",
            semester: 1,
            is_compulsory: true
        }

        nusmods_fe.add_modules([mod1, mod2]).then(() => {
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
                    <Grid columns={2} stackable celled>
                        <Grid.Row>
                            <Grid.Column textAlign="center">
                                <ModuleConstraints/>
                            </Grid.Column>
                            <Grid.Column textAlign="center">
                                <GlobalConstraints/>
                            </Grid.Column>
                        </Grid.Row>
                    </Grid>

                <Button onClick={onSubmit} color="green" attached="bottom">Run Solver</Button>
                </Segment>
            </Container>

            <Divider />

            <Container>
                <CodeDisplay code={smtlibInput} color="grey" headerText="SMTLIB2 Input (Debug)" />
            </Container>

            <Divider />

            <Container>
                <CodeDisplay code={smtlibOutput} color="black" headerText="SMTLIB2 Output (Debug)" />
            </Container>
        </div>
    );
}
