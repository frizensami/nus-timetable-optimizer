import React, { useState, useEffect } from 'react'
import './Solver.css'
import { Segment, Button, Container, Divider, Dropdown, Grid, Menu, Input, Form, Select, Header, Message, Card, Checkbox, Item, Transition } from 'semantic-ui-react'
import * as Constants from '../core/constants'
import { GlobalConstraintsList, defaultConstraints } from '../core/generic_timetable'

export interface GlobalConstraintsProps {
    onUpdateConstraints(newState: GlobalConstraintsList): any
}



/**
 * Responsible for setting constraints globally for all modules
 * */
export const GlobalConstraints: React.FC<GlobalConstraintsProps> = ({ onUpdateConstraints }) => {

    let [constraints, setConstraints] = useState<GlobalConstraintsList>(defaultConstraints);

    const generateTimeSelections = () => {
        const times: Array<any> = []
        for (let hour = Constants.DAY_START_HOUR; hour < Constants.DAY_END_HOUR; hour++) {
            const hourStr = hour <= 12 ? hour.toString() : (hour - 12).toString();
            const am_pm = hour >= 12 ? "PM" : "AM"
            times.push({ key: hour * 2, text: `${hourStr}:00 ${am_pm}`, value: hour * 2, })
            times.push({ key: hour * 2 + 1, text: `${hourStr}:30 ${am_pm}`, value: hour * 2 + 1, })
        }
        // Add the last time slot of the day
        const hour = Constants.DAY_END_HOUR;
        const am_pm = hour >= 12 ? "PM" : "AM"
        const hourStr = hour <= 12 ? hour.toString() : (hour - 12).toString();
        times.push({ key: hour * 2, text: `${hourStr}:00 ${am_pm}`, value: hour * 2, })

        return times

    }
    const timeSelections = generateTimeSelections();

    function _setConstraints(newState: GlobalConstraintsList) {
        onUpdateConstraints(newState)
        setConstraints(newState)
    }

    function updateMinWorkload(v: string) {
        const newState = { ...constraints, minWorkload: parseInt(v) }
        _setConstraints(newState);
    }

    function updateMaxWorkload(v: string) {
        const newState = { ...constraints, maxWorkload: parseInt(v) }
        _setConstraints(newState);
    }

    function toggleWorkloadActive() {
        const newState = { ...constraints, workloadActive: !constraints.workloadActive }
        _setConstraints(newState)
    }

    function toggleFreeDayActive() {
        const newState = { ...constraints, freeDayActive: !constraints.freeDayActive }
        _setConstraints(newState)
    }

    function toggleTimeConstraintActive() {
        const newState = { ...constraints, timeConstraintActive: !constraints.timeConstraintActive }
        _setConstraints(newState)
    }

    function setStartTime(v: any) {
        console.log(v);
        const hour = Math.floor(v / 2)
        const hourStr = hour < 10 ? "0" + hour.toString() : hour.toString();
        const min = v % 2 == 0 ? "00" : "30";
        const timeStr = `${hourStr}${min}`
        const newState = { ...constraints, startTime: timeStr }
        _setConstraints(newState)
    }


    function setEndTime(v: any) {
        console.log(v);
        const hour = Math.floor(v / 2)
        const hourStr = hour < 10 ? "0" + hour.toString() : hour.toString();
        const min = v % 2 == 0 ? "00" : "30";
        const timeStr = `${hourStr}${min}`
        const newState = { ...constraints, endTime: timeStr }
        _setConstraints(newState)
    }

    return (
        <div>
            <Header as="h3" textAlign="center"> Constraints </Header>

            <Divider />

            <Form>
                <Form.Group>
                    <Form.Field
                        id='form-input-min-workload'
                        control={Input}
                        label='Minimum Credits'
                        type="number"
                        defaultValue={defaultConstraints.minWorkload}
                        min="0"
                        step="1"
                        onChange={(e: any) => updateMinWorkload(e.target.value)}
                        width={5}
                        fluid
                    />
                    <Form.Field
                        id='form-input-max-workload'
                        control={Input}
                        label='Maximum Credits'
                        type="number"
                        defaultValue={defaultConstraints.maxWorkload}
                        min="0"
                        step="1"
                        onChange={(e: any) => updateMaxWorkload(e.target.value)}
                        fluid
                        width={5}
                    />
                    <Form.Field
                        control={Button}
                        label='Activate Constraint?'
                        toggle
                        active={constraints.workloadActive}
                        onClick={toggleWorkloadActive}
                        content={constraints.workloadActive ? "Yes" : "No"}
                        fluid
                        width={6}
                    />
                </Form.Group>


                <Divider />


                <Form.Group>
                    <Form.Field
                        id='form-input-earliest-start'
                        control={Select}
                        options={timeSelections}
                        defaultValue={timeSelections[0].key}
                        label='Earliest Lesson Start'
                        width={5}
                        fluid
                        search
                        onChange={(_: any, { value }: any) => setStartTime(value)}
                    />
                    <Form.Field
                        id='form-input-latest-end'
                        control={Select}
                        options={timeSelections}
                        defaultValue={timeSelections[timeSelections.length - 1].key}
                        label='Latest Lesson End'
                        fluid
                        width={5}
                        search
                        onChange={(_: any, { value }: any) => setEndTime(value)}
                    />
                    <Form.Field
                        control={Button}
                        label='Activate Constraint?'
                        toggle
                        active={constraints.timeConstraintActive}
                        onClick={toggleTimeConstraintActive}
                        content={constraints.timeConstraintActive ? "Yes" : "No"}
                        fluid
                        width={6}
                    />
                </Form.Group>


                <Divider />

                <Form.Group widths="equal">
                    <Form.Field
                        control={Button}
                        label='Force solver to find at least 1 free day (Mon - Fri): Activate Constraint?'
                        toggle
                        active={constraints.freeDayActive}
                        onClick={toggleFreeDayActive}
                        content={constraints.freeDayActive ? "Yes" : "No"}
                        fluid
                    />
                </Form.Group>





                <Divider />

            </Form>
        </div>
    );
}
