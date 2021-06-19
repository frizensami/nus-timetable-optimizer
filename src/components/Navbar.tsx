import React, { useState, useEffect } from 'react';
import { Input, Menu, Icon } from 'semantic-ui-react';
import { NavLink, useRouteMatch } from 'react-router-dom';

enum ActiveTab {
    SOLVER,
    HOW_TO_USE,
    ABOUT,
}

export const Navbar: React.FC = () => {
    let homeMatch = useRouteMatch({ path: '/', exact: true });
    let howMatch = useRouteMatch({ path: '/how', exact: true });
    let aboutMatch = useRouteMatch({ path: '/about', exact: true });

    return (
        <Menu stackable size="massive">
            <Menu.Item header>
                {' '}
                <Icon name="calendar alternate outline" /> <p> NUS Timetable Optimizer </p>{' '}
            </Menu.Item>
            <Menu.Item
                position="right"
                as={NavLink}
                to="/"
                activeClassName="selected"
                name="Solver"
                active={homeMatch !== null}
            />
            <Menu.Item
                as={NavLink}
                to="/how"
                activeClassName="selected"
                name="How To Use"
                active={howMatch !== null}
            />
            <Menu.Item
                as={NavLink}
                to="/about"
                activeClassName="selected"
                name="About"
                active={aboutMatch !== null}
            />
        </Menu>
    );
};
