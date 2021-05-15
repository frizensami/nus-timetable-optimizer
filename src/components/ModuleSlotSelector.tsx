import React, { useState, useEffect } from 'react';
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
import { ConstraintModule } from './ModuleConstraints';
import { Lesson, Module, GenericTimetable, GlobalConstraintsList } from '../core/generic_timetable';
import { groupBy, arrayEquals } from '../util/utils';

interface ModuleConstraintsProps {
    open: boolean;
    updateOpen(b: boolean): any;
    mod?: ConstraintModule;
    updateModuleSlotSelections(selections: LessonTypeConstraints): any;
    initialSlotSelections?: LessonTypeConstraints;
}

export type LessonTypeConstraints = Record<string, Array<any>>;

const ModuleSlotSelector: React.FC<ModuleConstraintsProps> = ({
    open,
    updateOpen,
    mod,
    updateModuleSlotSelections,
    initialSlotSelections,
}) => {
    // State of <lessonType> => [<lesson strings that are allowed>]
    let [lessonsSelected, setLessonsSelectioned] = useState<LessonTypeConstraints>({});

    const allModSelections: LessonTypeConstraints = parseMod();

    function parseMod(): LessonTypeConstraints {
        if (mod === undefined || mod.json === undefined) return {};

        console.log('initial selectiosn');
        console.log(initialSlotSelections);

        const data = mod.json;
        const semdata = data['semesterData'].find((v: any) => v.semester === mod.semester);
        const timetable = semdata['timetable'];

        let modSelections: LessonTypeConstraints = {};

        // Create generic lessons
        const grouped_lessontypes = groupBy(timetable, (v: any) => v['lessonType']);
        grouped_lessontypes.forEach((value: any, key: string, _: any) => {
            // Initialize the lessontype key
            let classes_for_lessontype = new Set();

            // For each lesson type, grab the "classNo" variable and add it to the set
            const lessons_for_lessontype = value;
            lessons_for_lessontype.forEach((lesson: any) =>
                classes_for_lessontype.add(lesson['classNo'])
            );

            // Map the class numbers to an array of select options
            const classes_array = Array.from(classes_for_lessontype).sort(function(a: any, b: any) {
                return a.localeCompare(b, undefined, {
                    numeric: true,
                    sensitivity: 'base',
                });
            });
            const select_options = classes_array.map((classNo: any) => {
                return {
                    key: key + '_' + classNo,
                    text: key + ' ' + classNo,
                    value: classNo,
                };
            });
            modSelections[key] = select_options;
        });

        return modSelections;
    }

    function updateConstraints(lessonType: string, lessons: Array<string>) {
        console.log('Updating state for lesson type' + lessonType + ' and lessons ');
        console.log(lessons);
        let newState = { ...lessonsSelected };
        if (lessons.length > 0) {
            newState[lessonType] = lessons;
        } else {
            delete newState[lessonType];
        }
        setLessonsSelectioned(newState);
    }

    function setOpen(b: boolean) {
        updateOpen(b);
    }

    function cancelSelections() {
        updateOpen(false);
    }

    function confirmSelections() {
        updateOpen(false);
        updateModuleSlotSelections(lessonsSelected);
    }

    return (
        <Modal
            size="small"
            centered={false}
            onClose={() => setOpen(false)}
            onOpen={() => setOpen(true)}
            open={open}
        >
            <Modal.Header>Restricting slots for {mod?.module_code}</Modal.Header>
            <Modal.Content>
                <Modal.Description>
                    <h5>
                        You may use this interface to select which lecture / tutorial / etc slots to
                        restrict the optimizer to.{' '}
                    </h5>
                    <p>
                        {' '}
                        The optimizer will <strong> only </strong> consider the slots you select
                        here during its optimization procedure. This can help you coordinate classes
                        with friends, work around any external commitments you have, etc.{' '}
                    </p>

                    <p>
                        {' '}
                        You can use{' '}
                        <a href="https://nusmods.com" target="_blank" rel="noreferrer">
                            NUSMods
                        </a>{' '}
                        to decide the class numbers that you want to consider.{' '}
                    </p>

                    <Form>
                        {Object.keys(allModSelections).map((lessonType, i) => {
                            return (
                                <Form.Group key={'form-group-lessontype' + i} widths="equal">
                                    <Form.Field
                                        key={'form-input-lessontype' + i}
                                        id={'form-input-lessontype' + i}
                                        control={Select}
                                        options={allModSelections[lessonType]}
                                        defaultValue={
                                            initialSlotSelections === undefined
                                                ? undefined
                                                : initialSlotSelections[lessonType]
                                        }
                                        placeholder="Unrestricted"
                                        fluid
                                        multiple
                                        selection
                                        search
                                        clearable
                                        label={
                                            mod?.module_code +
                                            ' ' +
                                            lessonType +
                                            ': only these class numbers will be considered during optimization. Leave blank for no restrictions.'
                                        }
                                        width={10}
                                        onChange={(_: any, { value }: any) =>
                                            updateConstraints(lessonType, value)
                                        }
                                    />
                                </Form.Group>
                            );
                        })}
                    </Form>
                </Modal.Description>
            </Modal.Content>

            <Modal.Actions>
                <Grid columns="equal">
                    <Grid.Column>
                        <Button fluid negative onClick={() => cancelSelections()}>
                            Cancel
                        </Button>
                    </Grid.Column>
                    <Grid.Column>
                        <Button
                            content="Confirm Selections"
                            fluid
                            onClick={() => confirmSelections()}
                            positive
                        />
                    </Grid.Column>
                </Grid>
            </Modal.Actions>
        </Modal>
    );
};

export default ModuleSlotSelector;
