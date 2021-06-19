import React, { useState } from 'react';
import './Solver.css';
import { Divider, Dimmer, Input, Form, Select, Header, Checkbox } from 'semantic-ui-react';
import * as Constants from '../core/constants';
import { GlobalConstraintsList } from '../core/generic_timetable';

export interface GlobalConstraintsProps {
    constraints: GlobalConstraintsList;
    onUpdateConstraints(newState: GlobalConstraintsList): any;
    numberOfModules: number;
}

/**
 * Responsible for setting constraints globally for all modules
 * */
const GlobalConstraints: React.FC<GlobalConstraintsProps> = ({
    constraints,
    onUpdateConstraints,
    numberOfModules,
}) => {
    /**
     * GENERATORS
     * */

    const freeDaySelections: Array<any> = [1, 2, 3, 4].map((n: number) => ({
        key: n,
        text: n,
        value: n,
    }));
    const freeDayofWeekSelection = [
        { key: 'Monday', text: 'Monday', value: 'Monday' },
        { key: 'Tuesday', text: 'Tuesday', value: 'Tuesday' },
        { key: 'Wednesday', text: 'Wednesday', value: 'Wednesday' },
        { key: 'Thursday', text: 'Thursday', value: 'Thursday' },
        { key: 'Friday', text: 'Friday', value: 'Friday' },
    ];

    const generateTimeSelections = () => {
        const times: Array<any> = [];
        for (let hour = Constants.DAY_START_HOUR; hour < Constants.DAY_END_HOUR; hour++) {
            const hourStr = hour <= 12 ? hour.toString() : (hour - 12).toString();
            const am_pm = hour >= 12 ? 'PM' : 'AM';
            times.push({
                key: hour * 2,
                text: `${hourStr}:00 ${am_pm}`,
                value: hour * 2,
            });
            times.push({
                key: hour * 2 + 1,
                text: `${hourStr}:30 ${am_pm}`,
                value: hour * 2 + 1,
            });
        }
        // Add the last time slot of the day
        const hour = Constants.DAY_END_HOUR;
        const am_pm = hour >= 12 ? 'PM' : 'AM';
        const hourStr = hour <= 12 ? hour.toString() : (hour - 12).toString();
        times.push({
            key: hour * 2,
            text: `${hourStr}:00 ${am_pm}`,
            value: hour * 2,
        });

        return times;
    };
    const timeSelections = generateTimeSelections();

    const generateLunchLengthSelections = () => {
        const times: Array<any> = [];
        for (let halfhours = 0; halfhours < 4 * 2 + 1; halfhours++) {
            const hourStr = Math.floor(halfhours / 2);
            const minStr = halfhours % 2 === 0 ? '0' : '30';
            const finalStr = `${hourStr} h ${minStr} min`;
            times.push({ key: halfhours, text: finalStr, value: halfhours });
        }
        return times;
    };
    const allLunchLengthSelections = generateLunchLengthSelections();

    /**
     * Setters / updaters
     * */

    function _setConstraints(newState: GlobalConstraintsList) {
        onUpdateConstraints(newState);
    }

    function updateMinWorkload(v: string) {
        const newState = { ...constraints, minWorkload: parseInt(v) };
        _setConstraints(newState);
    }

    function updateMaxWorkload(v: string) {
        const newState = { ...constraints, maxWorkload: parseInt(v) };
        _setConstraints(newState);
    }

    function toggleWorkloadActive() {
        const newState = {
            ...constraints,
            workloadActive: !constraints.workloadActive,
        };
        _setConstraints(newState);
    }

    function toggleFreeDayActive() {
        const newState = {
            ...constraints,
            freeDayActive: !constraints.freeDayActive,
        };
        _setConstraints(newState);
    }

    function toggleSpecificFreeDaysActive() {
        const newState = {
            ...constraints,
            specificFreeDaysActive: !constraints.specificFreeDaysActive,
        };
        _setConstraints(newState);
    }

    function toggleTimeConstraintActive() {
        const newState = {
            ...constraints,
            timeConstraintActive: !constraints.timeConstraintActive,
        };
        _setConstraints(newState);
    }

    function toggleCompactTimetable() {
        const newState = {
            ...constraints,
            preferCompactTimetable: !constraints.preferCompactTimetable,
        };
        _setConstraints(newState);
    }

    function toggleLunchBreakActive() {
        const newState = {
            ...constraints,
            lunchBreakActive: !constraints.lunchBreakActive,
        };
        _setConstraints(newState);
    }

    function setStartTime(v: any) {
        const timeStr = getTimeStr(v);
        const newState = { ...constraints, startTime: timeStr };
        _setConstraints(newState);
    }

    function setEndTime(v: any) {
        const timeStr = getTimeStr(v);
        const newState = { ...constraints, endTime: timeStr };
        _setConstraints(newState);
    }

    function setNumFreeDays(v: any) {
        const newState = { ...constraints, numRequiredFreeDays: v };
        _setConstraints(newState);
    }

    function setSpecificFreeDays(v: any) {
        // ["Monday", "Wednesday"] e.g.,
        const newState = { ...constraints, specificFreeDays: v };
        _setConstraints(newState);
    }

    function updateLunchStart(v: any) {
        const timeStr = getTimeStr(v);
        const newState = { ...constraints, lunchStart: timeStr };
        // updateLunchLengthList(newState.lunchStart, newState.lunchEnd)
        _setConstraints(newState);
    }

    function updateLunchEnd(v: any) {
        const timeStr = getTimeStr(v);
        const newState = { ...constraints, lunchEnd: timeStr };
        // updateLunchLengthList(newState.lunchStart, newState.lunchEnd)
        _setConstraints(newState);
    }

    function updateLunchLength(v: any) {
        const newState = { ...constraints, lunchHalfHours: v };
        _setConstraints(newState);
    }

    /*
     * UTILS
     */

    // Input: key in hour * 2 (+1 if half-hour offset) format (e.g., 8.30 am ==> key = 8 * 2 + 1)
    // Output: timestring in HHMM format
    function getTimeStr(v: any) {
        const hour = Math.floor(v / 2);
        const hourStr = hour < 10 ? '0' + hour.toString() : hour.toString();
        const min = v % 2 == 0 ? '00' : '30';
        const timeStr = `${hourStr}${min}`;
        return timeStr;
    }

    // Input: 24H HHMM, output:
    function getTimeKeyFromStr(t: string) {
        const hour = parseInt(t.substr(0, 2)) * 2;
        const final = hour + (t.substr(2, 4) === '30' ? 1 : 0);
        return final;
    }

    // Need to process a bit to set initial dropdown value
    function getLunchStartEndSelection() {
        const start = constraints.lunchStart; // eg 1100
        const end = constraints.lunchEnd; // eg 1500
        return [getTimeKeyFromStr(start), getTimeKeyFromStr(end)];
    }

    return (
        <div>
            <Header as="h3" textAlign="center">
                {' '}
                Constraints{' '}
            </Header>

            <Divider />

            <div>
                <Dimmer.Dimmable dimmed={numberOfModules === 0}>
                    <Form>
                        <Form.Group>
                            <Form.Field
                                id="form-input-min-workload"
                                control={Input}
                                label="Minimum Credits"
                                type="number"
                                defaultValue={constraints.minWorkload}
                                min={0}
                                step={1}
                                onChange={(e: any) => updateMinWorkload(e.target.value)}
                                width={5}
                            />
                            <Form.Field
                                id="form-input-max-workload"
                                control={Input}
                                label="Maximum Credits"
                                type="number"
                                defaultValue={constraints.maxWorkload}
                                min="0"
                                step="1"
                                onChange={(e: any) => updateMaxWorkload(e.target.value)}
                                width={5}
                            />
                            <Form.Field width={6}>
                                <div
                                    style={{
                                        display: 'flex',
                                        justifyContent: 'center',
                                        alignItems: 'center',
                                        height: '100%',
                                    }}
                                >
                                    <Checkbox
                                        label="Enabled"
                                        toggle
                                        checked={constraints.workloadActive}
                                        onClick={toggleWorkloadActive}
                                    />
                                </div>
                            </Form.Field>
                        </Form.Group>

                        <Divider />

                        <Form.Group>
                            <Form.Field
                                id="form-input-earliest-start"
                                control={Select}
                                options={timeSelections}
                                defaultValue={
                                    constraints.startTime
                                        ? getTimeKeyFromStr(constraints.startTime)
                                        : timeSelections[0].value
                                }
                                label="Earliest Lesson Start"
                                width={5}
                                search
                                onChange={(_: any, { value }: any) => setStartTime(value)}
                            />
                            <Form.Field
                                id="form-input-latest-end"
                                control={Select}
                                options={timeSelections}
                                defaultValue={
                                    constraints.endTime
                                        ? getTimeKeyFromStr(constraints.endTime)
                                        : timeSelections[timeSelections.length - 1].value
                                }
                                label="Latest Lesson End"
                                width={5}
                                search
                                onChange={(_: any, { value }: any) => setEndTime(value)}
                            />
                            <Form.Field width={6}>
                                <div
                                    style={{
                                        display: 'flex',
                                        justifyContent: 'center',
                                        alignItems: 'center',
                                        height: '100%',
                                    }}
                                >
                                    <Checkbox
                                        label="Enabled"
                                        toggle
                                        checked={constraints.timeConstraintActive}
                                        onClick={toggleTimeConstraintActive}
                                    />
                                </div>
                            </Form.Field>
                        </Form.Group>

                        <Divider />

                        <Form.Group widths="equal">
                            <Form.Field
                                id="form-input-num-free-days"
                                control={Select}
                                options={freeDaySelections}
                                defaultValue={
                                    constraints.numRequiredFreeDays || freeDaySelections[0].key
                                }
                                label="Number of Free Days Wanted"
                                width={10}
                                onChange={(_: any, { value }: any) => setNumFreeDays(value)}
                            />

                            <Form.Field width={6}>
                                <div
                                    style={{
                                        display: 'flex',
                                        justifyContent: 'center',
                                        alignItems: 'center',
                                        height: '100%',
                                    }}
                                >
                                    <Checkbox
                                        label="Enabled"
                                        toggle
                                        checked={constraints.freeDayActive}
                                        onClick={toggleFreeDayActive}
                                    />
                                </div>
                            </Form.Field>
                        </Form.Group>

                        <Divider />

                        <Form.Group widths="equal">
                            <Form.Field
                                id="form-input-which-fre-days"
                                control={Select}
                                options={freeDayofWeekSelection}
                                multiple
                                selection
                                defaultValue={constraints.specificFreeDays}
                                label="Specific Free Days Wanted"
                                width={10}
                                onChange={(_: any, { value }: any) => setSpecificFreeDays(value)}
                            />
                            <Form.Field width={6}>
                                <div
                                    style={{
                                        display: 'flex',
                                        justifyContent: 'center',
                                        alignItems: 'center',
                                        height: '100%',
                                    }}
                                >
                                    <Checkbox
                                        label="Enabled"
                                        toggle
                                        checked={constraints.specificFreeDaysActive}
                                        onClick={toggleSpecificFreeDaysActive}
                                    />
                                </div>
                            </Form.Field>
                        </Form.Group>

                        <Divider />

                        <Form.Group>
                            <Form.Field
                                id="form-input-lunch-start"
                                control={Select}
                                options={timeSelections}
                                defaultValue={getLunchStartEndSelection()[0]}
                                label="Lunch Period Start"
                                width={8}
                                search
                                onChange={(_: any, { value }: any) => updateLunchStart(value)}
                            />
                            <Form.Field
                                id="form-input-lunch-end"
                                control={Select}
                                options={timeSelections}
                                defaultValue={getLunchStartEndSelection()[1]}
                                label="Lunch Period End"
                                width={8}
                                search
                                onChange={(_: any, { value }: any) => updateLunchEnd(value)}
                            />
                        </Form.Group>

                        <Form.Group>
                            <Form.Field
                                id="form-input-num-lunch-hours"
                                control={Select}
                                label="Minimum Lunch Duration within Lunch Period"
                                options={allLunchLengthSelections}
                                defaultValue={constraints.lunchHalfHours}
                                onChange={(_: any, { value }: any) => updateLunchLength(value)}
                                width={10}
                            />
                            <Form.Field width={6}>
                                <div
                                    style={{
                                        display: 'flex',
                                        justifyContent: 'center',
                                        alignItems: 'center',
                                        height: '100%',
                                    }}
                                >
                                    <Checkbox
                                        label="Enabled"
                                        toggle
                                        checked={constraints.lunchBreakActive}
                                        onClick={toggleLunchBreakActive}
                                    />
                                </div>
                            </Form.Field>
                        </Form.Group>

                        <Divider />

                        <Form.Group widths="equal">
                            <Form.Field
                                control={Checkbox}
                                label="Make timetable as compact as possible? Warning: optimizer might become very slow!"
                                toggle
                                checked={constraints.preferCompactTimetable}
                                onClick={toggleCompactTimetable}
                            />
                        </Form.Group>

                        <Divider />

                        <Dimmer active={numberOfModules === 0}>
                            <Header as="h3" inverted>
                                Add at least one module before changing constraints.
                            </Header>
                        </Dimmer>
                    </Form>
                </Dimmer.Dimmable>
            </div>
        </div>
    );
};

export default GlobalConstraints;
