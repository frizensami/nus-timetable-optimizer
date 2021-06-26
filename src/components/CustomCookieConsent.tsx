import React from 'react';
import CookieConsent from 'react-cookie-consent';
import { initGA, removeGA } from '../util/analytics';

export const CustomCookieConsent: React.FC = () => {
    function handleAcceptCookie() {
        initGA();
    }

    function handleDeclineCookie() {
        removeGA();
    }

    return (
        <CookieConsent
            location="top"
            buttonText="I understand"
            enableDeclineButton
            declineButtonText="I decline"
            overlay={true}
            overlayStyle={{ 'background-color': 'rgba(0, 0, 0, 0.7' }}
            buttonClasses="ui primary padded button"
            declineButtonClasses="ui padded button"
            disableButtonStyles={true}
            buttonStyle={{ margin: '5px' }}
            declineButtonStyle={{ margin: '5px' }}
            onAccept={handleAcceptCookie}
            onDecline={handleDeclineCookie}
        >
            <h3>
                {' '}
                We use Google Analytics cookies to improve your user experience and the optimizer's
                speed over time.{' '}
            </h3>
        </CookieConsent>
    );
};
