import React, { useState, useEffect } from 'react'

import { TimetableOutput } from '../core/timetable_to_smtlib2'
import { Segment, Button, Container, Divider, Grid } from 'semantic-ui-react'
import { GenericTimetable } from '../core/generic_timetable'
import { Z3Manager, Z3Callbacks } from '../core/z3_manager'
import { NUSModsFrontend, ModuleToAdd } from '../frontends/nusmods_frontend'
import { CodeDisplay } from './CodeDisplay'
import { ModuleConstraints, ConstraintModule } from './ModuleConstraints'
import { GlobalConstraints } from './GlobalConstraints'
import './Solver.css'


export const Solver: React.FC<{ onNewTimetable(timetable: any): any }> = ({ onNewTimetable }) => {

    let [smtlibInput, setSmtlibInput] = useState<string>("No input yet.");
    let [smtlibOutput, setSmtlibOutput] = useState<string>("No output yet.");
    let [modules, setModules] = useState<Array<ModuleToAdd>>([]);

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

        nusmods_fe.add_modules(modules).then(() => {
            console.log(nusmods_fe);
            const gt: GenericTimetable = nusmods_fe.create_timetable(5, 10);
            Z3Manager.init(gt, callbacks);
            Z3Manager.initZ3();
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

                    <Button onClick={onSubmit} color="green" attached="top">Run Solver</Button>
                    <Grid columns={2} stackable celled>
                        <Grid.Row>
                            <Grid.Column textAlign="center">
                                <ModuleConstraints onModulesChange={onModulesChange} />
                            </Grid.Column>
                            <Grid.Column textAlign="center">
                                <GlobalConstraints />
                            </Grid.Column>
                        </Grid.Row>
                    </Grid>

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
