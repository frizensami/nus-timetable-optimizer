import React, { useState, useEffect } from 'react'
import './Solver.css'
import { Segment, Button, Container, Divider, Dropdown, Grid, Menu, Input, Select, Header, Message, Card, Checkbox, Item, Transition } from 'semantic-ui-react'
import { NUSModsFrontend } from '../frontends/nusmods_frontend'

interface ModuleConstraintsProps {
    onModulesChange(mods: Array<ConstraintModule>): any
}

export interface ConstraintModule {
    module_code: string,
    acad_year: string,
    semester: number,
    json?: any
    required: boolean
}

/**
 * Responsible for setting constraints individually for all selected modules.
 * Also contains a selector (combined here to keep state contained) for the modules
 * */
export const ModuleConstraints: React.FC<ModuleConstraintsProps> = ({ onModulesChange }) => {
    let ay_xs: Array<any> = [{ key: 1, text: "AY 2020-2021", value: 1 }]
    let sem_xs: Array<any> = [{ key: 1, text: "Sem 1", value: 1 }, { key: 2, text: "Sem 2", value: 2 }]
    const defaultAyValue = 1
    const defaultSemValue = 1

    let [moduleText, setModuleText] = useState("")
    let [ayValue, setAyText] = useState(defaultAyValue)
    let [semValue, setSemText] = useState(defaultSemValue)
    let [modules, setModules] = useState<Array<ConstraintModule>>([])
    let [showModuleAddError, setShowModuleAddError] = useState(false);
    let [showModuleAddSuccess, setShowModuleAddSuccess] = useState(false);
    let [activeErrorCancelTimeout, setActiveErrorCancelTimeout] = useState<any>(undefined)
    let [activeSuccessCancelTimeout, setActiveSuccessCancelTimeout] = useState<any>(undefined)

    /*
     * Try to add a module to the current list of modules
     */
    function handleClick() {
        const ay = ay_xs.find(x => x.value == ayValue);
        const sem = sem_xs.find(x => x.value == semValue);
        console.log(`${moduleText} - ${ay.text} - ${sem.text}`);
        let mod: ConstraintModule = { module_code: moduleText.toUpperCase(), acad_year: ay.text.split(' ')[1], semester: semValue, required: true }

        const containsModAlready: boolean = modules.some((m: ConstraintModule) => m.module_code === mod.module_code);
        if (containsModAlready) {
            console.log("Couldn't add module, exists already")
            setShowModuleAddSuccess(false);
            setShowModuleAddError(true);
            cancelErrorAfterInterval();
            return;
        }

        NUSModsFrontend.read_module_json(mod.module_code, mod.acad_year, mod.semester).then((moduleJson: any) => {
            console.log(moduleJson)
            if (Object.keys(moduleJson).length === 0) {
                console.log("Couldn't add module!")
                setShowModuleAddSuccess(false);
                setShowModuleAddError(true);
                cancelErrorAfterInterval();
            } else {
                mod.json = moduleJson
                console.log("Successfully added module!")
                setShowModuleAddSuccess(true);
                setShowModuleAddError(false);
                cancelSucessAfterInterval();
                let mods = modules.concat(mod);
                setModules(mods);
                onModulesChange(mods);
            }
        })
    }

    function cancelErrorAfterInterval() {
        if (activeErrorCancelTimeout !== undefined) clearTimeout(activeErrorCancelTimeout);
        let t = setTimeout(() => {
            setShowModuleAddError(false);
        }, 3000)
        setActiveErrorCancelTimeout(t);
    }

    function cancelSucessAfterInterval() {
        if (activeSuccessCancelTimeout !== undefined) clearTimeout(activeSuccessCancelTimeout);
        let t = setTimeout(() => {
            setShowModuleAddSuccess(false);
        }, 3000)
        setActiveSuccessCancelTimeout(t);
    }

    function toggleRequired(mod: ConstraintModule) {
        const mods = modules.map((m: ConstraintModule) => {
            if (m !== mod) {
                return m;
            } else {
                m.required = !m.required;
                return m;
            }
        });
        setModules(mods);
        onModulesChange(mods);
    }

    function removeModule(mod: ConstraintModule) {
        let newmods = modules.filter(m => m !== mod)
        setModules(newmods)
        onModulesChange(newmods);
    }

    function onKeyPress(event: any) {
        if (event.key === 'Enter') {
            handleClick();
        }
    }

    return (
        <div>
            <Header as="h3" textAlign="center"> Module Selector </Header>
            <Grid stackable textAlign="center">


                { /* Display module selector */}
                <Grid.Row>
                    <Input action type='text' onChange={(e) => setModuleText(e.target.value)} onKeyPress={onKeyPress} placeholder='Type module code'>
                        <input />
                        <Select compact options={ay_xs} defaultValue={defaultAyValue} onChange={(e, { value }) => setAyText(value as number)} />
                        <Select compact options={sem_xs} defaultValue={defaultSemValue} onChange={(e, { value }) => setSemText(value as number)} />
                        <Button type="submit" onClick={handleClick}> Add Module</Button>
                    </Input>
                </Grid.Row>

                { /* Display error messages */}
                <Grid.Row>
                    <Transition visible={showModuleAddError} animation='fade' duration={1000}>
                        <Message negative>
                            <Message.Header>{"The module you specified doesn't exist or is already added."}</Message.Header>
                            <p>Please try another module or check the academic year / semester in NUSMods </p>
                        </Message>
                    </Transition>


                    <Transition visible={showModuleAddSuccess} animation='fade' duration={1000}>
                        <Message positive>
                            <Message.Header>{"Module added!"}</Message.Header>
                        </Message>
                    </Transition>
                    <Divider />
                </Grid.Row>

                { /* Conditional display of header */}
                {modules.length > 0 &&
                    <Header as='h3' textAlign='center'> Selected Modules </Header>
                }


                { /* Display each module as a card within the grid */}
                {
                    modules.map((mod: ConstraintModule, idx: number) => {
                        return (

                            <Grid.Row key={idx} columns="equal">
                                <Grid.Column textAlign="center" width={16}>
                                    <Card centered fluid>
                                        <Card.Content>
                                            <Card.Header> {mod.module_code + " " + mod.json["title"]} </Card.Header>
                                            <Card.Meta> {"AY " + mod.acad_year + " Semester " + mod.semester} </Card.Meta>
                                        </Card.Content>
                                        <Card.Content extra>
                                            <Grid stackable textAlign="center">
                                                <Grid.Row columns="equal">

                                                    <Grid.Column width={8}>
                                                        <Button toggle active={mod.required} onClick={() => toggleRequired(mod)}>
                                                            {mod.required ? "Required" : "Optional"}
                                                        </Button>
                                                    </Grid.Column>

                                                    <Grid.Column width={8}>
                                                        <Button basic color='red' onClick={() => removeModule(mod)}>
                                                            Remove Module
                                                    </Button>

                                                    </Grid.Column>
                                                </Grid.Row>
                                            </Grid>
                                        </Card.Content>
                                    </Card>
                                </Grid.Column>
                            </Grid.Row>
                        )

                    })
                }
            </Grid>
        </div>
    )
}