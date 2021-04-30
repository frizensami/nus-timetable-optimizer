import { LessonWeek, Lesson, Module, GenericTimetable } from '../core/generic_timetable'
import { render, screen } from '@testing-library/react';

test('Can create a new Lesson as expected', () => {
    // Y M D H M (10:30)
    const start_d = new Date(2018, 11, 12, 10, 30);
    const end_d = new Date(2018, 11, 12, 12, 30);
    let lesson = new Lesson("1", "Lecture", [[start_d, end_d]], ["Monday"], LessonWeek.ALL);
    // console.log(lesson);
    expect(lesson).toBeDefined();
});

test('Can create a new Module as expected', () => {
    // Y M D H M (10:30)
    const start_d = new Date(2018, 11, 12, 10, 30);
    const end_d = new Date(2018, 11, 12, 12, 30);
    let lesson = new Lesson("1", "Lecture", [[start_d, end_d]], ["Monday"], LessonWeek.ALL);

    let mod = new Module("CS3203", 5, [lesson], true);
    
    expect(mod).toBeDefined();
});

test('Can create a new Timetable as expected', () => {
    // Y M D H M (10:30)
    const start_d = new Date(2018, 11, 12, 10, 30);
    const end_d = new Date(2018, 11, 12, 12, 30);
    let lesson = new Lesson("1", "Lecture", [[start_d, end_d]], ["Monday"], LessonWeek.ALL);
    let mod = new Module("CS3203", 5, [lesson], true);
    let gt = new GenericTimetable([mod], 5, 10);
    
    expect(gt).toBeDefined();
});




