import { filter, map, join, length } from "ramda";

// ========================================================
// Error handling
export const isError = (x: any): x is Error => x instanceof Error;

// Type predicate that warrants that an array does not contain errors.
// Needed for safeFL
export const hasNoError = <T1>(x: Array<T1 | Error>): x is T1[] => length(filter(isError, x)) === 0;
export const getErrorMessages = (x: any[]): string =>
    join("\n", map((x) => 
        isError(x) ? JSON.stringify(x.message) : "", filter(isError, x)));

// Make a safe version of f: apply f to x but check if x is an error before applying it.
export const safeF: <T1, T2>(f: (x: T1) => T2) => (x: T1 | Error) => T2 | Error = 
    (f) => (x) => 
        isError(x) ? x :
        f(x);

export const safeF2: <T1, T2, T3>(f: (x: T1, y: T2) => T3) => (x : T1 | Error, y : T2 | Error) => T3 | Error =
    (f) => (x, y) =>
        isError(x) ? x :
        isError(y) ? y :
        f(x, y)


// Same as safeF but for a function that accepts an array of values
// NOTE: we must use an annotation of the form Array<T1 | Error> instead of (T1 | Error)[]
// this is a syntactic restriction of TypeScript.
export const safeFL: <T1, T2>(f: (xs: T1[]) => T2) => (xs: Array<T1 | Error>) => T2 | Error =
    <T1, T2>(f: (xs: T1[]) => T2) =>
    (xs: Array<T1 | Error>): T2 | Error =>
        hasNoError(xs) ? f(xs) : Error(getErrorMessages(xs));

