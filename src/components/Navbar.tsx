import React, { useState, useEffect } from 'react';
import { Input, Menu, Icon } from 'semantic-ui-react';
import { NavLink, withRouter } from 'react-router-dom';

enum ActiveTab {
    SOLVER,
    HOW_TO_USE,
    ABOUT,
}

export const Navbar: React.FC = () => {
    let [activeItem, setActiveItem] = useState<ActiveTab>(ActiveTab.SOLVER);

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
                active={activeItem === ActiveTab.SOLVER}
                onClick={() => setActiveItem(ActiveTab.SOLVER)}
            />
            <Menu.Item
                as={NavLink}
                to="/how"
                name="How To Use"
                active={activeItem === ActiveTab.HOW_TO_USE}
                onClick={() => setActiveItem(ActiveTab.HOW_TO_USE)}
            />
            <Menu.Item
                as={NavLink}
                to="/about"
                name="About"
                active={activeItem === ActiveTab.ABOUT}
                onClick={() => setActiveItem(ActiveTab.ABOUT)}
            />
        </Menu>
    );
};
