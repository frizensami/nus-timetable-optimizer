import React, { useState, useEffect } from 'react';
import logo from './logo.svg';
import { Route, Switch } from 'react-router-dom';
import { Navbar } from './components/Navbar';
import { SolverApp } from './components/SolverApp';
import { HowToUse } from './components/HowToUse';
import { About } from './components/About';
// import './App.css';
// import 'semantic-ui-less/semantic.less'
import 'semantic-ui-css/semantic.min.css';

import Timetable from './components/Timetable';
import { Solver } from './components/Solver';
import { Divider } from 'semantic-ui-react';
import PageNotFound from './components/PageNotFound';
import { MediaContextProvider } from './components/Responsive';
import { usePageTracking } from './util/analytics';

function App() {
    usePageTracking();

    return (
        <div className="App">
            <MediaContextProvider>
                <div className="ui basic segment">
                    <Navbar />
                    <Switch>
                        <Route path="/" exact component={SolverApp} />

                        <Route path="/how" component={HowToUse} />

                        <Route path="/about" component={About} />

                        <Route component={PageNotFound} />
                    </Switch>
                </div>
            </MediaContextProvider>
        </div>
    );
}

export default App;
