import React, { useState } from 'react';
import { Segment, Table, Header, Dimmer } from 'semantic-ui-react'

interface TimetableProps {
    start_hour: number,
    end_hour: number,
    timetable: any
}

function Timetable({ start_hour, end_hour, timetable }: TimetableProps) {
    // let [dimmerActive, setDimmerActive] = useState(false);
    let hours: Array<String> = [];
    const days = 5;
    const daysOfWeek = ["MON", "TUE", "WED", "THU", "FRI"]
    console.log("timetable")
    console.log(timetable)
    for (let hour = start_hour; hour < end_hour; hour++) {
        // For each hour we need the hour and the 1/2 hour mark
        if (hour < 10) {
            hours.push(`0${hour}00`)
            hours.push(`0${hour}30`)
        } else {
            hours.push(`${hour}00`)
            hours.push(`${hour}30`)
        }
    }

    return (
        <div className="timetable">
            <Dimmer.Dimmable dimmed={!timetable.is_sat}>
                <Segment raised style={{ overflow: 'auto', maxWidth: "100%" }}>
                    <Header as='h2' textAlign="center">Timetable Output</Header>
                    <Table unstackable celled definition striped>
                        <Table.Header>
                            <Table.Row textAlign='center'>
                                <Table.HeaderCell />
                                {
                                    hours.map((hour, i) => {
                                        return <Table.HeaderCell key={i}>{hour}</Table.HeaderCell>
                                    })
                                }
                            </Table.Row>
                        </Table.Header>

                        <Table.Body>
                            {
                                // Runs for each day
                                [...Array(days)].map((_, i1) => {
                                    return (
                                        <Table.Row key={i1}>
                                            <Table.Cell key={i1} textAlign='center'>{daysOfWeek[i1]}</Table.Cell>
                                            {hours.map((_, i2) => {
                                                if (Object.keys(timetable).length === 0) {
                                                    return <Table.Cell key={(2 ** i1) * (3 ** i2)} textAlign='center'>{""}</Table.Cell>;
                                                } else {
                                                    return <Table.Cell key={(2 ** i1) * (3 ** i2)} textAlign='center'>{timetable.tt[i1][i2]}</Table.Cell>;
                                                }
                                            })}
                                        </Table.Row>
                                    )
                                })
                            }
                        </Table.Body>
                    </Table>
                </Segment>
                <Dimmer active={!timetable.is_sat}>
                    <Header as='h2' inverted color='red'>
                        No valid timetable found: run the solver or change your constraints.
                    </Header>
                </Dimmer>
            </Dimmer.Dimmable>
        </div>
    );
}

export default Timetable;
