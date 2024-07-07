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
    let [nusmodsLink, setNusmodsLink] = useState('');

    function onNewTimetable(timetable: any, nusmodsLink: string) {
        setTT(timetable);
        setNusmodsLink(nusmodsLink);
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

            <Message positive>
                <Message.Header as="p" style={{ textAlign: 'center' }}>
                    Updated for AY 2024/25! Please report any feedback to{' '}
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
                    <br />
                </Message.Header>
            </Message>

            <Suspense
                fallback={
                    <Container textAlign="center">
                        <strong>Loading Timetable...</strong>
                    </Container>
                }
            >
                <Timetable start_hour={8} end_hour={22} timetable={tt} nusmodsLink={nusmodsLink} />
            </Suspense>
            <Divider />
            <Solver onNewTimetable={onNewTimetable} />
        </div>
    );
};
