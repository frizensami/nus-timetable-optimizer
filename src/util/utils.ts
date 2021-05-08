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
  list.forEach((item) => {
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
  const hashNum = hashCode(str);
  const color = randomColor(
    {
      seed: hashNum,
      alpha: 0.6,
      format: 'rgba',
      luminosity: 'light',
    }
  );
  return color
}

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
    for(let i = 0; i < s.length; i++) 
          h = Math.imul(31, h) + s.charCodeAt(i) | 0;

    return h;
}
