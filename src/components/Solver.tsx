import React, { useState, useEffect } from 'react'

import { TimetableOutput } from '../core/timetable_to_smtlib2'
import { Segment, Button, Container, Divider, Grid, Loader, Dimmer } from 'semantic-ui-react'
import { GenericTimetable } from '../core/generic_timetable'
import { Z3Manager, Z3Callbacks } from '../core/z3_manager'
import { NUSModsFrontend, ModuleToAdd } from '../frontends/nusmods_frontend'
import { CodeDisplay } from './CodeDisplay'
import { ModuleConstraints, ConstraintModule } from './ModuleConstraints'
import { GlobalConstraints, GlobalConstraintsList, defaultConstraints } from './GlobalConstraints'
import './Solver.css'

enum Z3State {
    PRE_INIT = 0,
    INITIALIZED = 1,
    SOLVING = 2,
}


export const Solver: React.FC<{ onNewTimetable(timetable: any): any }> = ({ onNewTimetable }) => {

    let [smtlibInput, setSmtlibInput] = useState<string>("No input yet.");
    let [smtlibOutput, setSmtlibOutput] = useState<string>("No output yet.");
    let [modules, setModules] = useState<Array<ModuleToAdd>>([]);
    let [z3State, setZ3State] = useState<Z3State>(Z3State.PRE_INIT);
    let [constraints, setConstraints] = useState<GlobalConstraintsList>(defaultConstraints);



    function onZ3Initialized() {
        setZ3State(Z3State.INITIALIZED)
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
        setZ3State(Z3State.INITIALIZED)
        onNewTimetable(timetable);
    }

    const callbacks: Z3Callbacks = {
        onZ3Initialized: onZ3Initialized,
        onSmtlib2InputCreated: updateInputSmtlib2,
        onOutput: onOutput,
        onTimetableOutput: onTimetableOutput
    }


    // Runs once to init the z3 module
    useEffect(() => {
        setTimeout(() => Z3Manager.initZ3(callbacks), 1000);
    }, []);

    // Runs on button pressed
    function onSubmit() {
        console.log("Initializing z3 worker");
        // console.log(worker)
        let nusmods_fe = new NUSModsFrontend();

        nusmods_fe.add_modules(modules).then(() => {
            console.log(nusmods_fe);
            const gt: GenericTimetable = nusmods_fe.create_timetable(constraints.minWorkload, constraints.maxWorkload, constraints.freeDayActive);
            Z3Manager.loadTimetable(gt);
            setZ3State(Z3State.SOLVING);
            Z3Manager.solve()
        });

    }

    function onModulesChange(mods: Array<ConstraintModule>) {
        console.log(`onModulesChange: ${mods}`)
        setModules(mods.map((mod: ConstraintModule) => {
            return {
                module_code: mod.module_code,
                acad_year: mod.acad_year,
                semester: mod.semester,
                is_compulsory: mod.required
            }
        }));
    }

    return (
        <div className="solver">

            <Container>
                <Segment raised>

                    <h3 className="ui center aligned header"> Modules & Constraints </h3>

                    {

                        {
                            0: <Segment raised>
                                <Button disabled attached="top">Solver Loading</Button>,
                                <Dimmer active>
                                    <Loader content='Solver Initializing... (this can take one or two minutes)' />
                                </Dimmer>
                            </Segment>,
                            1: <Button onClick={onSubmit} primary size="big" attached="top">Run Solver</Button>,
                            2: <Segment raised>
                                <Button disabled attached="top">Solver Running</Button>,
                                <Dimmer active>
                                    <Loader content='Solver Running...' />
                                </Dimmer>
                            </Segment>,
                        }[z3State]
                    }



                    <Grid columns="equal" stackable celled>
                        <Grid.Row>
                            <Grid.Column textAlign="center">
                                <ModuleConstraints onModulesChange={onModulesChange} />
                            </Grid.Column>
                            <Grid.Column textAlign="center">
                                <GlobalConstraints onUpdateConstraints={setConstraints} />
                            </Grid.Column>
                        </Grid.Row>
                    </Grid>

                </Segment>
            </Container>

            <Divider />

            <Container>
                <CodeDisplay code={smtlibInput} theme="dark" headerText="Solver SMTLIB2 Input (Debug)" />
            </Container>

            <Divider />

            <Container>
                <CodeDisplay code={smtlibOutput} theme="light" headerText="Solver SMTLIB2 Output (Debug)" />
            </Container>
        </div>
    );
}
