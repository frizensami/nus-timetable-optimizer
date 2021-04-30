import React from 'react';
import { Segment, Table, Header } from 'semantic-ui-react'

interface TimetableProps {
    start_hour: number,
    end_hour: number,
}

function Timetable({ start_hour, end_hour }: TimetableProps) {
    let hours: Array<String> = [];
    const days = 5;
    const daysOfWeek = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
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
            <Segment raised>
                <Header as='h2' textAlign="center">Timetable Output</Header>
                <Table celled definition striped>
                    <Table.Header>
                        <Table.Row textAlign='center'>
                                <Table.HeaderCell/>
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
                                        <Table.Cell key={i1}>{daysOfWeek[i1]}</Table.Cell>
                                        {hours.map((_, i2) => {
                                            return <Table.Cell key={(2**i1)*(3**i2)} textAlign='center'>{"CS3203"}</Table.Cell>
                                        })}
                                    </Table.Row>
                                )
                            })
                        }
                    </Table.Body>
                </Table>
            </Segment>
        </div>
    );
}

export default Timetable;
