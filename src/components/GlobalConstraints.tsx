import React, { useState, useEffect } from 'react'
import './Solver.css'
import { Segment, Button, Container, Divider, Dropdown, Grid, Menu, Input, Form, Select, Header, Message, Card, Checkbox, Item, Transition } from 'semantic-ui-react'

export interface GlobalConstraintsList {
    workloadActive: boolean,
    minWorkload: number,
    maxWorkload: number
    freeDayActive: boolean
}

export interface GlobalConstraintsProps {
    onUpdateConstraints(newState: GlobalConstraintsList): any
}

export const defaultConstraints: GlobalConstraintsList = {
    workloadActive: false,
    minWorkload: 16,
    maxWorkload: 30,
    freeDayActive: false
};

/**
 * Responsible for setting constraints globally for all modules
 * */
export const GlobalConstraints: React.FC<GlobalConstraintsProps> = ({ onUpdateConstraints }) => {

    let [constraints, setConstraints] = useState<GlobalConstraintsList>(defaultConstraints);

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

    return (
        <div>
            <Header as="h3" textAlign="center"> Constraints </Header>

            <Divider />

            <Form textAlign>
                <Form.Group>
                    <Form.Field
                        id='form-input-min-workload'
                        control={Input}
                        label='Minimum Workload (MCs)'
                        type="number"
                        placeholder='16'
                        min="0"
                        step="1"
                        onChange={(e: any) => updateMinWorkload(e.target.value)}
                        width={6}
                        fluid
                    />
                    <Form.Field
                        id='form-input-max-workload'
                        control={Input}
                        label='Maximum Workload (MCs)'
                        type="number"
                        placeholder='30'
                        min="0"
                        step="1"
                        onChange={(e: any) => updateMaxWorkload(e.target.value)}
                        fluid
                        width={6}
                    />
                    <Form.Field
                        control={Button}
                        label='&nbsp;'
                        toggle
                        active={constraints.workloadActive}
                        onClick={toggleWorkloadActive}
                        content={constraints.workloadActive ? "Active" : "Inactive"}
                        fluid
                        width={4}
                    />

                </Form.Group>


                <Divider />

                <Form.Group widths="equal">
                    <Form.Field
                        control={Button}
                        label='Force solver to find at least 1 free day (Mon - Fri)? (likely to make days longer)'
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
