import React, { Suspense, useState, useEffect } from 'react';
import logo from './logo.svg';
// import './App.css';
// import 'semantic-ui-less/semantic.less'

import { Solver } from './Solver';
import { Divider, Message, Container } from 'semantic-ui-react';
import { Media } from './Responsive';
const Timetable = React.lazy(() => import('./Timetable'));

export const SolverApp: React.FC = () => {
    let [tt, setTT] = useState({});

    function onNewTimetable(timetable: any) {
        setTT(timetable);
    }

    return (
        <div>
            <Media lessThan="md">
                {(mediaClassNames, renderChildren) => {
                    return renderChildren ? (
                        <Message error>
                            <Message.Header as="p" style={{ textAlign: 'center' }}>
                                This application is best viewed on a desktop computer.
                            </Message.Header>
                        </Message>
                    ) : null;
                }}
            </Media>

            <Message info>
                <Message.Header as="p" style={{ textAlign: 'center' }}>
                    The NUS Timetable Optimizer is in <em> Beta Testing Mode</em>. Please report any
                    errors or feedback to{' '}
                    <a href="mailto:sriramsami@nus.edu.sg?subject=NUS Timetable Optimizer Feedback">
                        sriramsami@nus.edu.sg
                    </a>{' '}
                    or{' '}
                    <a
                        href="https://github.com/frizensami/nus-timetable-optimizer/issues"
                        target="_blank"
                        rel="noreferrer"
                    >
                        open an Issue on GitHub
                    </a>
                    .
                    <br />
                    Modules for AY2021/22 should be updated in sync with NUSMods on 20th June 2021.
                </Message.Header>
            </Message>

            <Suspense
                fallback={
                    <Container textAlign="center">
                        <strong>Loading Timetable...</strong>
                    </Container>
                }
            >
                <Timetable start_hour={8} end_hour={22} timetable={tt} />
            </Suspense>
            <Divider />
            <Solver onNewTimetable={onNewTimetable} />
        </div>
    );
};
