import React, { useState, useEffect } from 'react'
import './Solver.css'
import { Segment, Button, Container, Divider, Dropdown, Grid, Menu, Input, Select, Header, Message } from 'semantic-ui-react'
import { NUSModsFrontend } from '../frontends/nusmods_frontend'

interface ConstraintModule {
    module_code: string,
    acad_year: string,
    semester: number
}

/**
 * Responsible for setting constraints individually for all selected modules.
 * Also contains a selector (combined here to keep state contained) for the modules
 * */
export const ModuleConstraints: React.FC<{}> = () => {
    let ay_xs: Array<any> = [{ key: 1, text: "AY 2020-2021", value: 1 }]
    let sem_xs: Array<any> = [{ key: 1, text: "Sem 1", value: 1 }, { key: 2, text: "Sem 2", value: 2 }]
    const defaultAyValue = 1
    const defaultSemValue = 1

    let [moduleText, setModuleText] = useState("")
    let [ayValue, setAyText] = useState(defaultAyValue)
    let [semValue, setSemText] = useState(defaultSemValue)
    let [modules, setModules] = useState([])
    let [showModuleAddError, setShowModuleAddError] = useState(false);
    let [showModuleAddSuccess, setShowModuleAddSuccess] = useState(false);

    /*
     * Try to add a module to the current list of modules
     */
    function handleClick() {
        const ay = ay_xs.find(x => x.value == ayValue);
        const sem = sem_xs.find(x => x.value == semValue);
        console.log(`${moduleText} - ${ay.text} - ${sem.text}`);
        let mod: ConstraintModule = { module_code: moduleText.toUpperCase(), acad_year: ay.text.split(' ')[1], semester: semValue }
        NUSModsFrontend.read_module_json(mod.module_code, mod.acad_year, mod.semester).then((moduleJson: any) => {
            console.log(moduleJson)
            if (Object.keys(moduleJson).length === 0) {
                console.log("Couldn't add module")
                setShowModuleAddSuccess(false);
                setShowModuleAddError(true);
            } else {
                console.log("Success!")
                setShowModuleAddSuccess(true);
                setShowModuleAddError(false);
            }
        })
    }

    return (
        <div>
            <Header as="h4" textAlign="center"> Modules </Header>
            <Grid stackable textAlign="center">
                <Grid.Row>
                    <Input action type='text' onChange={(e) => setModuleText(e.target.value)} placeholder='Type module code'>
                        <input />
                        <Select compact options={ay_xs} defaultValue={defaultAyValue} onChange={(e, { value }) => setAyText(value as number)} />
                        <Select compact options={sem_xs} defaultValue={defaultSemValue} onChange={(e, { value }) => setSemText(value as number)} />
                        <Button onClick={handleClick}>Add Module</Button>
                    </Input>
                </Grid.Row>

                <Grid.Row>
                    <Message negative {...showModuleAddError === true ? { visible: true } : { hidden: true }}>
                        <Message.Header>{"The module you specified doesn't exist"}</Message.Header>
                        <p>Please try another module or check the academic year / semester in NUSMods </p>
                    </Message>
                    <Message positive {...showModuleAddSuccess === true ? { visible: true } : { hidden: true }}>
                        <Message.Header>{"Module added!"}</Message.Header>
                    </Message>
                </Grid.Row>
            </Grid>
        </div>
    )
}
