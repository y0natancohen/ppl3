import { strict as assert } from 'assert';
import { makeVarDecl, makeVarRef,
         isBoolExp, isNumExp, isPrimOp, isStrExp, isVarDecl, isVarRef, isSetExp,
         isAppExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isLitExp, isProcExp, isProgram,
         parse, unparse } from './L4-ast';
import { isEnv, makeExtEnv, applyEnv, theGlobalEnv, globalEnvAddBinding } from './L4-env-box';
import { makeClosure, makeCompoundSExp, makeEmptySExp, makeSymbolSExp } from './L4-value-box';
import { evalParse } from './L4-eval-box';

// ========================================================
// TESTS Env
{
    // todo: fix test
    // Extended envs are defined with a frame (vars, vals)
    const env1 = makeExtEnv(["a", "b"], [1, 2], theGlobalEnv);
    const env2 = makeExtEnv(["a"], [3], env1);

    assert.ok(isEnv(theGlobalEnv));
    assert.ok(isEnv(env1));
    assert.equal(applyEnv(env1, "a"), 1);
    assert.equal(applyEnv(env2, "a"), 3);
    assert.equal(applyEnv(env2, "b"), 2);
}

// ========================================================
// TESTS Parser

// Atomic
assert.ok(isNumExp(parse("1")));
assert.ok(isBoolExp(parse("#t")));
assert.ok(isVarRef(parse("x")));
assert.ok(isStrExp(parse('"a"')));
assert.ok(isPrimOp(parse(">")));
assert.ok(isPrimOp(parse("=")));
assert.ok(isPrimOp(parse("string=?")));
assert.ok(isPrimOp(parse("eq?")));
assert.ok(isPrimOp(parse("cons")));

// Program
assert.ok(isProgram(parse("(L4 (define x 1) (> (+ x 1) (* x x)))")));

// Define
assert.ok(isDefineExp(parse("(define x 1)")));
{
    let def = parse("(define x 1)");
    if (isDefineExp(def)) {
        assert.ok(isVarDecl(def.var));
        assert.ok(isNumExp(def.val));
    }
}

// Application
assert.ok(isAppExp(parse("(> x 1)")));
assert.ok(isAppExp(parse("(> (+ x x) (* x x))")));

// L2 - If, Proc
assert.ok(isIfExp(parse("(if #t 1 2)")));
assert.ok(isIfExp(parse("(if (< x 2) x 2)")));
assert.ok(isProcExp(parse("(lambda () 1)")));
assert.ok(isProcExp(parse("(lambda (x) x x)")));

// L3 - Literal, Let
assert.ok(isLetExp(parse("(let ((a 1) (b #t)) (if b a (+ a 1)))")));

assert.ok(isLitExp(parse("'a")));
assert.ok(isLitExp(parse("'()")));
assert.ok(isLitExp(parse("'(1)")));

// L3 - Literal, Let
assert.ok(isLetExp(parse("(let ((a 1) (b #t)) (if b a (+ a 1)))")));

// L4-box - letrec, set!
assert.ok(isLetrecExp(parse("(letrec ((e (lambda (x) x))) (e 2))")));
assert.ok(isSetExp(parse("(set! x (+ 1 2))")));


/*
console.log(parse("(set! x (+ 1 2))"));
console.log(parse("'a"));
console.log(parse("'\"b\""));
console.log(parse("'(s \"a\")"));
console.log(parse("'()"));
*/

// ========================================================
// TESTS Unparse

// Atomic
["1", "#t", "x", '"a"', ">", "=", "string=?", "eq?", "cons"].forEach(
  concrete => assert.equal(unparse(parse(concrete)), concrete)
);

// Program
{
  const p1 = "(L4 (define x 1) (> (+ x 1) (* x x)))"
  assert.equal(unparse(parse(p1)), p1); 
}

// Define
{
  const d1 = "(define x 1)";
  assert.equal(unparse(parse(d1)), d1); 
}

// Application
{
  const a1 = "(> x 1)";
  const a2 = "(> (+ x x) (* x x))";
  assert.equal(unparse(parse(a1)), a1); 
  assert.equal(unparse(parse(a2)), a2); 
}

// L2 - If, Proc
{
  const i1 = "(if #t 1 2)";
  const i2 = "(if (< x 2) x 2)";
  const pr1 = "(lambda () 1)";
  const pr2 = "(lambda (x) x x)";
  assert.equal(unparse(parse(i1)), i1); 
  assert.equal(unparse(parse(i2)), i2); 
  assert.equal(unparse(parse(pr1)), pr1); 
  assert.equal(unparse(parse(pr2)), pr2); 
}

// L3 - Literal, Let
{
  const l1 = "(let ((a 1) (b #t)) (if b a (+ a 1)))";
  assert.equal(unparse(parse(l1)), l1); 

  ["'a", "'()", "'(1)", "'(1 . 2)", "'(1 2 . 3)"].forEach(
      lit => assert.equal(unparse(parse(lit)), lit)); 
  
  // Test normalization of dotted pairs
  const dp1 = "'(1 . (2 . 3))";
  assert.equal(unparse(parse(dp1)), "'(1 2 . 3)")
}

// L4 - letrec, set! (set! is defined in AST - not in eval)
{
  // letrec val must be procedures
  const lr1 = "(letrec ((f (lambda (x) x))) (f 2))";
  assert.equal(unparse(parse(lr1)), lr1); 

  // **** L4-box is different from L4 on letrec
  // letrec val can also be non procedures
  const lr2 = "(letrec ((a 1) (b #t)) (if b a (+ a 1)))";
  assert.deepEqual(evalParse(lr2), 1);

  const se1 = "(set! x (+ 1 2))";
  assert.equal(unparse(parse(se1)), se1); 

}

// ========================================================
// Test L4 Box interpreter

// ========================================================
// TESTS GlobalEnv
globalEnvAddBinding("m", 1);
assert.deepEqual(applyEnv(theGlobalEnv, "m"), 1);

// ========================================================
// TESTS

// Test each data type literals
assert.deepEqual(evalParse("1"), 1);
assert.deepEqual(evalParse("#t"), true);
assert.deepEqual(evalParse("#f"), false);
assert.deepEqual(evalParse("'a"), makeSymbolSExp("a"));
assert.deepEqual(evalParse('"a"'), "a");
assert.deepEqual(evalParse("'()"), makeEmptySExp());
assert.deepEqual(evalParse("'(1 2)"), makeCompoundSExp(1, makeCompoundSExp(2, makeEmptySExp())));
assert.deepEqual(evalParse("'(1 (2))"), makeCompoundSExp(1, makeCompoundSExp(makeCompoundSExp(2, makeEmptySExp()), makeEmptySExp())));

// Test primitives
/*
;; <prim-op>  ::= + | - | * | / | < | > | = | not |  eq? | string=?
;;                  | cons | car | cdr | list? | number?
;;                  | boolean? | symbol? | string?      ##### L3
*/
assert.deepEqual(evalParse("(+ 1 2)"), 3);
assert.deepEqual(evalParse("(- 2 1)"), 1);
assert.deepEqual(evalParse("(* 2 3)"), 6);
assert.deepEqual(evalParse("(/ 4 2)"), 2);
assert.deepEqual(evalParse("(< 4 2)"), false);
assert.deepEqual(evalParse("(> 4 2)"), true);
assert.deepEqual(evalParse("(= 4 2)"), false);
assert.deepEqual(evalParse("(not #t)"), false);
assert.deepEqual(evalParse("(eq? 'a 'a)"), true);
assert.deepEqual(evalParse('(string=? "a" "a")'), true);
assert.deepEqual(evalParse("(cons 1 '())"), makeCompoundSExp(1, makeEmptySExp()));
assert.deepEqual(evalParse("(cons 1 '(2))"), makeCompoundSExp(1, makeCompoundSExp(2, makeEmptySExp())));
assert.deepEqual(evalParse("(car '(1 2))"), 1);
assert.deepEqual(evalParse("(cdr '(1 2))"), makeCompoundSExp(2, makeEmptySExp()));
assert.deepEqual(evalParse("(cdr '(1))"), makeEmptySExp());
assert.deepEqual(evalParse("(list? '(1))"), true);
assert.deepEqual(evalParse("(list? '())"), true);
assert.deepEqual(evalParse("(number? 1)"), true);
assert.deepEqual(evalParse("(number? #t)"), false);
assert.deepEqual(evalParse("(boolean? #t)"), true);
assert.deepEqual(evalParse("(boolean? 0)"), false);
assert.deepEqual(evalParse("(symbol? 'a)"), true);
assert.deepEqual(evalParse('(symbol? "a")'), false);
assert.deepEqual(evalParse("(string? 'a)"), false);
assert.deepEqual(evalParse('(string? "a")'), true);
assert.deepEqual(evalParse('(pair? "a")'), false);
assert.deepEqual(evalParse('(pair? (cons 1 2))'), true);
assert.deepEqual(evalParse("(pair? '(1))"), true);

// Test define
assert.deepEqual(evalParse("(L4 (define x 1) (+ x x))"), 2);
assert.deepEqual(evalParse("(L4 (define x 1) (define y (+ x x)) (* y y))"), 4);

// Test if
assert.deepEqual(evalParse('(if (string? "a") 1 2)'), 1);
assert.deepEqual(evalParse('(if (not (string? "a")) 1 2)'), 2);

// Test proc
assert.deepEqual(evalParse("(lambda (x) x)"), 
                 makeClosure([makeVarDecl("x")], [makeVarRef("x")], theGlobalEnv));

// Test apply proc
assert.deepEqual(evalParse("((lambda (x) (* x x)) 2)"), 4);
assert.deepEqual(evalParse("(L4 (define square (lambda (x) (* x x))) (square 3))"), 9);
assert.deepEqual(evalParse("(L4 (define f (lambda (x) (if (> x 0) x (- 0 x)))) (f -3))"), 3);

// L4 BOX @@
// Recursive procedure = WORKS as in Scheme - without letrec
assert.deepEqual(evalParse("(L4 (define f (lambda (x) (if (= x 0) 1 (* x (f (- x 1)))))) (f 3))"), 6);

// Recursion with letrec
assert.deepEqual(evalParse(`
(letrec ((f (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))))
  (f 5))
`), 120);

// Preserve bound variables
assert.deepEqual(evalParse(`
(L4 (define fact
        (letrec ((f (lambda (n)
                      (if (= n 0)
                          1
                          (* n (f (- n 1)))))))
          f))
    (fact 5))
`), 120);

// Accidental capture of the z variable if no renaming - works without renaming in env eval.
assert.deepEqual(evalParse(`
(L4
    (define z (lambda (x) (* x x)))
    (((lambda (x) (lambda (z) (x z)))
      (lambda (w) (z w)))
     2))`),
4);

// Y-combinator
assert.deepEqual(evalParse(`
(L4 (((lambda (f) (f f))
      (lambda (fact)
        (lambda (n)
          (if (= n 0)
              1
              (* n ((fact fact) (- n 1)))))))
     6))`),
    720);

// L4 higher order functions
assert.deepEqual(evalParse(`
(L4 (define map
      (lambda (f l)
        (if (eq? l '())
          l
          (cons (f (car l)) (map f (cdr l))))))
    (map (lambda (x) (* x x))
      '(1 2 3)))`),
    evalParse("'(1 4 9)"));

assert.deepEqual(evalParse(`
(L4 (define empty? (lambda (x) (eq? x '())))
    (define filter
      (lambda (pred l)
        (if (empty? l)
          l
          (if (pred (car l))
              (cons (car l) (filter pred (cdr l)))
              (filter pred (cdr l))))))
    (filter (lambda (x) (not (= x 2)))
        '(1 2 3 2)))`),
    evalParse("'(1 3)"))

assert.deepEqual(evalParse(`
(L4 (define compose (lambda (f g) (lambda (x) (f (g x)))))
    ((compose not number?) 2))`),
    false);

// @@ Properly capture variables in closures
assert.deepEqual(evalParse(`
(L4 (define makeAdder (lambda (n) (lambda (y) (+ y n))))
    (define a6 (makeAdder 6))
    (define a7 (makeAdder 7))
    (+ (a6 1) (a7 1)))
    `),
    15);

assert.deepEqual(evalParse(`
(L4 (define makeCounter (lambda () (let ((c 0)) (lambda () (set! c (+ c 1)) c))))
    (define c1 (makeCounter))
    (define c2 (makeCounter))
    (+ (+ (c1) (c1))
       (+ (c2) (c2))))
    `),
    6);

// Mutual recursion
const oddEven = `
(L4
  (define odd? (lambda (n) (if (= n 0) #f (even? (- n 1)))))
  (define even? (lambda (n) (if (= n 0) #t (odd? (- n 1)))))
  (and (odd? 5) (even? 6)))`;
assert.deepEqual(evalParse(oddEven), true);


