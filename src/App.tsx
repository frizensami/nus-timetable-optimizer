import React, { useState, useEffect } from 'react'
import logo from './logo.svg';
import { BrowserRouter as Router, Route } from "react-router-dom"
import { Navbar } from './components/Navbar'
import { SolverApp } from './components/SolverApp'
import { HowToUse } from './components/HowToUse'
import { About } from './components/About'
// import './App.css';             
import 'semantic-ui-less/semantic.less'

import Timetable from './components/Timetable'
import { Solver } from './components/Solver'
import { Divider } from 'semantic-ui-react'

function App() {
        return (
                <div className="App">
                        <div className="ui basic segment">
                                <Router>
                                        <Navbar />
                                        <Route
                                                path="/"
                                                exact
                                                render={() =>
                                                        <SolverApp />}
                                        />

                                        <Route
                                                path="/how"
                                                exact
                                                render={() =>
                                                        <HowToUse />}
                                        />

                                        <Route
                                                path="/about"
                                                exact
                                                render={() =>
                                                        <About />}
                                        />

                                </Router>
                        </div>
                </div>
        );
}

export default App;
