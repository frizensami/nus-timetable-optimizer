import React, { useState, useEffect } from 'react';
import './Solver.css';
import {
    Segment,
    Button,
    Container,
    Divider,
    Dropdown,
    Grid,
    Icon,
    Modal,
    List,
    Menu,
    Input,
    Form,
    Select,
    Header,
    Message,
    Card,
    Checkbox,
    Item,
    Transition,
} from 'semantic-ui-react';
import { NUSModsFrontend } from '../frontends/nusmods_frontend';
import { getRandomColorFromString } from '../util/utils';
import ModuleSlotSelector, { LessonTypeConstraints } from './ModuleSlotSelector';

interface ModuleConstraintsProps {
    onModulesChange(mods: Array<ConstraintModule>): any;
}

export interface ConstraintModule {
    module_code: string;
    acad_year: string;
    semester: number;
    json?: any;
    required: boolean;
    lessonConstraints?: LessonTypeConstraints; // JSON after constraints have
}

/**
 * Responsible for setting constraints individually for all selected modules.
 * Also contains a selector (combined here to keep state contained) for the modules
 * */
const ModuleConstraints: React.FC<ModuleConstraintsProps> = ({ onModulesChange }) => {
    let ay_xs: Array<any> = [{ key: 1, text: '2020-2021', value: 1 }];
    let sem_xs: Array<any> = [
        { key: 1, text: '1', value: 1 },
        { key: 2, text: '2', value: 2 },
    ];
    const defaultAyValue = 1;
    const defaultSemValue = 1;

    let [moduleText, setModuleText] = useState('');
    let [ayValue, setAyText] = useState(defaultAyValue);
    let [semValue, setSemText] = useState(defaultSemValue);
    let [modules, setModules] = useState<Array<ConstraintModule>>([]);
    let [showModuleAddError, setShowModuleAddError] = useState(false);
    let [showModuleAddSuccess, setShowModuleAddSuccess] = useState(false);
    let [activeErrorCancelTimeout, setActiveErrorCancelTimeout] = useState<any>(undefined);
    let [activeSuccessCancelTimeout, setActiveSuccessCancelTimeout] = useState<any>(undefined);
    let [open, setOpen] = useState(false);
    let [open2, setOpen2] = useState(false);
    let [openSlotSelector, setOpenSlotSelector] = useState(false);
    let [selectedMod, setSelectedMod] = useState<ConstraintModule | undefined>(undefined);

    /*
     * Try to add a module to the current list of modules
     */
    function handleClick() {
        const ay = ay_xs.find(x => x.value == ayValue);
        const sem = sem_xs.find(x => x.value == semValue);
        console.log(`${moduleText} - ${ay.text} - ${sem.text}`);
        let mod: ConstraintModule = {
            module_code: moduleText.toUpperCase(),
            acad_year: ay.text,
            semester: semValue,
            required: true,
        };

        const containsModAlready: boolean = modules.some(
            (m: ConstraintModule) => m.module_code === mod.module_code
        );
        if (containsModAlready) {
            console.log("Couldn't add module, exists already");
            setShowModuleAddSuccess(false);
            setShowModuleAddError(true);
            cancelErrorAfterInterval();
            return;
        }

        NUSModsFrontend.read_module_json(mod.module_code, mod.acad_year, mod.semester).then(
            (moduleJson: any) => {
                console.log(moduleJson);
                if (Object.keys(moduleJson).length === 0) {
                    console.log("Couldn't add module!");
                    setShowModuleAddSuccess(false);
                    setShowModuleAddError(true);
                    cancelErrorAfterInterval();
                } else {
                    mod.json = moduleJson;
                    const data = mod.json;
                    const semdata = data['semesterData'].find(
                        (v: any) => v.semester === mod.semester
                    );
                    const timetable = semdata['timetable'];
                    // If any lesson doesn't have a weeks array, show the modal
                    if (timetable.some((lesson: any) => !Array.isArray(lesson.weeks))) {
                        setOpen(true);
                        let mods = modules.concat(mod);
                        setModules(mods);
                        onModulesChange(mods);
                    } else if (modules.length > 0 && mod.semester !== modules[0].semester) {
                        console.log('Diff sem');
                        // Our new module is from a different semester than the rest
                        setOpen2(true);
                        let mods = modules.concat(mod);
                        setModules(mods);
                        onModulesChange(mods);
                    } else {
                        console.log('Successfully added module!');
                        setShowModuleAddSuccess(true);
                        setShowModuleAddError(false);
                        cancelSucessAfterInterval();
                        let mods = modules.concat(mod);
                        setModules(mods);
                        onModulesChange(mods);
                    }
                }
            }
        );
    }

    function removeLatestModuleAndClose() {
        let mods = modules.slice(0, -1);
        setModules(mods);
        onModulesChange(mods);
        setOpen(false);
        setOpen2(false);
    }

    function cancelErrorAfterInterval() {
        if (activeErrorCancelTimeout !== undefined) clearTimeout(activeErrorCancelTimeout);
        let t = setTimeout(() => {
            setShowModuleAddError(false);
        }, 3000);
        setActiveErrorCancelTimeout(t);
    }

    function cancelSucessAfterInterval() {
        if (activeSuccessCancelTimeout !== undefined) clearTimeout(activeSuccessCancelTimeout);
        let t = setTimeout(() => {
            setShowModuleAddSuccess(false);
        }, 3000);
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
        let newmods = modules.filter(m => m !== mod);
        setModules(newmods);
        onModulesChange(newmods);
    }

    function manualSelect(mod: ConstraintModule) {
        setSelectedMod(mod);
        setOpenSlotSelector(true);
    }

    function updateOpenSlotSelector() {
        setOpenSlotSelector(false);
    }

    function updateModuleSlotSelections(selections: LessonTypeConstraints) {
        const mods = modules.map((m: ConstraintModule) => {
            if (m !== selectedMod) {
                return m;
            } else {
                if (selections === undefined || Object.keys(selections).length === 0) {
                    m.lessonConstraints = undefined;
                } else {
                    m.lessonConstraints = selections;
                }
                return m;
            }
        });
        setModules(mods);
        onModulesChange(mods);
    }

    // { /* Display error messages */}
    // <Grid.Row>

    // </Grid.Row>

    return (
        <div>
            <Header as="h3" textAlign="center">
                {' '}
                Module Selector{' '}
            </Header>

            <Divider />

            {/* Display module selector */}
            <Form>
                <Form.Group>
                    <Form.Field
                        id="form-input-module-name"
                        control={Input}
                        label="Module Code"
                        placeholder="(e.g., CS3230)"
                        onChange={(e: any) => setModuleText(e.target.value)}
                        fluid
                        width={5}
                    />
                    <Form.Field
                        control={Select}
                        options={ay_xs}
                        defaultValue={defaultAyValue}
                        label="Academic Year"
                        onChange={(_: any, { value }: any) => setAyText(value as number)}
                        width={4}
                        fluid
                    />
                    <Form.Field
                        control={Select}
                        options={sem_xs}
                        defaultValue={defaultSemValue}
                        label="Semester"
                        onChange={(_: any, { value }: any) => setSemText(value as number)}
                        width={3}
                        fluid
                    />
                    <Form.Field
                        id="form-button-control-public"
                        control={Button}
                        content="Add Module"
                        primary
                        onClick={handleClick}
                        label="&nbsp;"
                        fluid
                        width={4}
                    />
                </Form.Group>
            </Form>

            <Transition visible={showModuleAddError} animation="fade" duration={1000}>
                <Message negative>
                    <Message.Header>
                        {"The module you specified doesn't exist or is already added."}
                    </Message.Header>
                    <p>
                        Please try another module or check the academic year / semester in NUSMods{' '}
                    </p>
                </Message>
            </Transition>

            <Transition visible={showModuleAddSuccess} animation="fade" duration={1000}>
                <Message positive>
                    <Message.Header>{'Module added!'}</Message.Header>
                </Message>
            </Transition>

            <Grid stackable centered textAlign="center">
                {/* Conditional display of header */}
                {modules.length > 0 && (
                    <Grid.Row>
                        <Divider />
                        <Header as="h3" textAlign="center">
                            {' '}
                            Selected Modules{' '}
                        </Header>
                        <Divider />
                    </Grid.Row>
                )}

                {/* Display each module as a card within the grid */}
                <Transition.Group duration={1000}>
                    {modules.map((mod: ConstraintModule, idx: number) => {
                        let color = getRandomColorFromString(mod.module_code);
                        return (
                            <Grid.Row centered key={idx} columns="equal">
                                <Grid.Column textAlign="center" width={16}>
                                    <Card centered fluid>
                                        <Card.Content>
                                            <Button
                                                size="mini"
                                                floated="right"
                                                negative
                                                icon
                                                onClick={() => removeModule(mod)}
                                            >
                                                <Icon name="close" />
                                            </Button>
                                            <Card.Header>
                                                {' '}
                                                <Icon
                                                    name="square outline"
                                                    size="tiny"
                                                    style={{
                                                        backgroundColor: color,
                                                    }}
                                                />{' '}
                                                {mod.module_code + ' ' + mod.json['title']}{' '}
                                            </Card.Header>
                                            <Card.Meta>
                                                {' '}
                                                {'AY ' +
                                                    mod.acad_year +
                                                    ' | Semester ' +
                                                    mod.semester +
                                                    ' | Workload: ' +
                                                    mod.json['moduleCredit'] +
                                                    ' MC'}{' '}
                                            </Card.Meta>
                                            <Message
                                                visible={mod.lessonConstraints !== undefined}
                                                hidden={mod.lessonConstraints === undefined}
                                                info
                                            >
                                                <p>
                                                    {' '}
                                                    You have restricted the possible slots for this
                                                    module.{' '}
                                                </p>
                                            </Message>
                                        </Card.Content>
                                        <Card.Content extra>
                                            <Grid stackable textAlign="center">
                                                <Grid.Row columns="equal">
                                                    <Grid.Column textAlign="center" width={8}>
                                                        <Button
                                                            fluid
                                                            primary
                                                            onClick={() => manualSelect(mod)}
                                                        >
                                                            Restrict Slots
                                                        </Button>
                                                    </Grid.Column>

                                                    <Grid.Column textAlign="center" width={8}>
                                                        <Button
                                                            fluid
                                                            toggle
                                                            active={mod.required}
                                                            onClick={() => toggleRequired(mod)}
                                                        >
                                                            {mod.required
                                                                ? 'Compulsory Module'
                                                                : 'Optional Module'}
                                                        </Button>
                                                    </Grid.Column>
                                                </Grid.Row>
                                            </Grid>
                                        </Card.Content>
                                    </Card>
                                </Grid.Column>
                            </Grid.Row>
                        );
                    })}
                </Transition.Group>
            </Grid>

            <Modal onClose={() => setOpen(false)} onOpen={() => setOpen(true)} open={open}>
                <Modal.Header>
                    The module you are adding does not follow the traditional NUS Academic Semester
                    Calendar.
                </Modal.Header>
                <Modal.Content>
                    <Modal.Description>
                        <p>
                            Would you like to <strong>skip</strong> adding this module, or just{' '}
                            <strong>
                                assume that the module takes place every week this semester?
                            </strong>
                        </p>
                    </Modal.Description>
                </Modal.Content>
                <Modal.Actions>
                    <Grid columns="equal">
                        <Grid.Column>
                            <Button fluid negative onClick={() => removeLatestModuleAndClose()}>
                                Skip
                            </Button>
                        </Grid.Column>
                        <Grid.Column>
                            <Button
                                content="Assume weekly"
                                fluid
                                onClick={() => setOpen(false)}
                                positive
                            />
                        </Grid.Column>
                    </Grid>
                </Modal.Actions>
            </Modal>

            <Modal onClose={() => setOpen2(false)} onOpen={() => setOpen2(true)} open={open2}>
                <Modal.Header>
                    The module you are adding is from a different semester than the rest of the
                    modules.
                </Modal.Header>
                <Modal.Content>
                    <Modal.Description>
                        <p>
                            Would you like to <strong>skip</strong> adding this module, or{' '}
                            <strong>add it anyway?</strong>
                        </p>
                    </Modal.Description>
                </Modal.Content>
                <Modal.Actions>
                    <Grid columns="equal">
                        <Grid.Column>
                            <Button fluid negative onClick={() => removeLatestModuleAndClose()}>
                                Skip
                            </Button>
                        </Grid.Column>
                        <Grid.Column>
                            <Button
                                content="Add anyway"
                                fluid
                                onClick={() => setOpen2(false)}
                                positive
                            />
                        </Grid.Column>
                    </Grid>
                </Modal.Actions>
            </Modal>

            <ModuleSlotSelector
                open={openSlotSelector}
                updateOpen={updateOpenSlotSelector}
                mod={selectedMod}
                updateModuleSlotSelections={updateModuleSlotSelections}
                initialSlotSelections={selectedMod?.lessonConstraints}
            />
        </div>
    );
};

export default ModuleConstraints;
