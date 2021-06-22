/**
 * @description
 * Takes an Array<V>, and a grouping function,
 * and returns a Map of the array grouped by the grouping function.
 *
 * @param list An array of type V.
 * @param keyGetter A Function that takes the the Array type V as an input, and returns a value of type K.
 *                  K is generally intended to be a property key of V.
 *
 * @returns Map of the array grouped by the grouping function.
 */
export function groupBy(list: Array<any>, keyGetter: Function) {
    const map = new Map();
    list.forEach(item => {
        const key = keyGetter(item);
        const collection = map.get(key);
        if (!collection) {
            map.set(key, [item]);
        } else {
            collection.push(item);
        }
    });
    return map;
}

/**
 * Swaps the keys and values of an object
 * */
export function flipRecord(obj: any): any {
    const ret: any = {};
    Object.keys(obj).forEach(key => {
        ret[obj[key]] = key;
    });
    return ret;
}

/**
 * Used for module name to color
 * */
let randomColor = require('randomcolor'); // import the script
export function getRandomColorFromString(str: string) {
    const hashNum = hashCodeMurmur(str);
    const color = randomColor({
        seed: hashNum,
        alpha: 0.6,
        format: 'rgba',
        luminosity: 'light',
    });
    return color;
}

const MurmurHash3 = require('imurmurhash');
const hashState = new MurmurHash3('', 42);

const hashCodeMurmur = function(s: string): number {
    const res = hashState.hash(s).result();
    hashState.reset();
    return res;
};

/**
 * Returns a hash code for a string.
 * (Compatible to Java's String.hashCode())
 *
 * The hash code for a string object is computed as
 *     s[0]*31^(n-1) + s[1]*31^(n-2) + ... + s[n-1]
 * using number arithmetic, where s[i] is the i th character
 * of the given string, n is the length of the string,
 * and ^ indicates exponentiation.
 * (The hash value of the empty string is zero.)
 *
 * @param {string} s a string
 * @return {number} a hash code value for the given string.
 */
const hashCode = function hashCode(s: string): number {
    let h = 0;
    for (let i = 0; i < s.length; i++) h = (Math.imul(31, h) + s.charCodeAt(i)) | 0;

    return h;
};

/**
 * Check for array equality. I can't believe this isn't a builtin.
 * */
export function arrayEquals(a: any, b: any) {
    return (
        Array.isArray(a) &&
        Array.isArray(b) &&
        a.length === b.length &&
        a.every((val, index) => val === b[index])
    );
}

// Assign an array of properties to an object - creating nested levels
// E.g., nestObject({}, [a, b, c]) ==> {a: {b: c}}
export function nestObject(obj: any, keyPath: Array<any>) {
    const value = keyPath[keyPath.length - 1];
    let lastKeyIndex = Math.max(0, keyPath.length - 2);
    for (var i = 0; i < lastKeyIndex; ++i) {
        let key = keyPath[i];
        if (!(key in obj)) {
            obj[key] = {};
        }
        obj = obj[key];
    }
    obj[keyPath[lastKeyIndex]] = value;
}

/** *
 * Usage:
 * const ids = new StringIdGenerator();

ids.next(); // 'a'
ids.next(); // 'b'
ids.next(); // 'c'

// ...
ids.next(); // 'z'
ids.next(); // 'A'
ids.next(); // 'B'

// ...
ids.next(); // 'Z'
ids.next(); // 'aa'
ids.next(); // 'ab'
ids.next(); // 'ac'
 *
 * */
export class StringIdGenerator {
    _chars: any;
    _nextId: any;
    constructor(chars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ') {
        this._chars = chars;
        this._nextId = [0];
    }

    next() {
        const r = [];
        for (const char of this._nextId) {
            r.unshift(this._chars[char]);
        }
        this._increment();
        return r.join('');
    }

    _increment() {
        for (let i = 0; i < this._nextId.length; i++) {
            const val = ++this._nextId[i];
            if (val >= this._chars.length) {
                this._nextId[i] = 0;
            } else {
                return;
            }
        }
        this._nextId.push(0);
    }

    *[Symbol.iterator]() {
        while (true) {
            yield this.next();
        }
    }
}
