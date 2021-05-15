import React, { Suspense, useState, useEffect } from 'react'
import logo from './logo.svg';
// import './App.css';             
// import 'semantic-ui-less/semantic.less'

import { Solver } from './Solver'
import { Divider, Message, Container } from 'semantic-ui-react'
const Timetable = React.lazy(() => import('./Timetable'));

export const SolverApp: React.FC = () => {
    let [tt, setTT] = useState({})

    function onNewTimetable(timetable: any) {
        setTT(timetable);
    }

    return (
        <div>
            <Message error>
                <Message.Header as="p" style={{ "textAlign": "center" }}>
                    The NUS Timetable Optimizer is in <em> Beta Testing Mode</em>. Please report any errors or feedback to <a href="mailto:sriramsami@nus.edu.sg?subject=NUS Timetable Optimizer Feedback">sriramsami@nus.edu.sg</a>.
            </Message.Header>

            </Message>

            <Suspense fallback={<Container textAlign="center"><strong>Loading Timetable...</strong></Container>}>
                <Timetable start_hour={8} end_hour={22} timetable={tt} />
            </Suspense>
            <Divider />
            <Solver onNewTimetable={onNewTimetable} />
        </div>
    );
}
