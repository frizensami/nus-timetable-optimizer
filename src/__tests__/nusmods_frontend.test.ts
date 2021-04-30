import { NUSModsFrontend } from '../frontends/nusmods_frontend'
import { CS3203 } from './consts_json'


test('A module is loaded asynchronously correctly', async () => {
    // This is a really cool hack to mock the fetch we use internally to resolve to the CS3203 constant json we have 
    // @ts-ignore
    global.fetch = jest.fn(() =>
        Promise.resolve({
            json: () => Promise.resolve(CS3203),
        })
    );

    let nusmods_fe = new NUSModsFrontend();
    let mod1 = {
        module_code: "CS3203",
        acad_year: "2020-2021",
        semester: 1,
        is_compulsory: true
    }
    await nusmods_fe.add_module(mod1);
    // console.log(nusmods_fe)
    expect(nusmods_fe.modules).toHaveLength(1);
    expect(nusmods_fe.modules[0].lessons['Lecture']).toHaveLength(1);
    expect(nusmods_fe.modules[0].lessons['Recitation']).toHaveLength(2);
});
