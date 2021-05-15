import React from 'react'
import { Container, Image } from 'semantic-ui-react'

const PageNotFound: React.FC<{}> = () => {
    return (
        <Container textAlign="center">
            <Image fluid src='/404.jpeg' />
        </Container>
    )
}

export default PageNotFound
