{-| Annah is a tiny language that serves to illustrate how various programming
    constructs can be desugared to lambda calculus.  The most sophisticated
    feature that Annah supports is desugaring mutually recursive data types
    to non-recursive lambda expressions.

    Under the hood, all Annah expressions are translated to a minimalist
    implementation of the calculus of constructions called Morte, which only
    supports non-recursive lambda expressions and their types.  You can find
    the Morte compiler and library here:

    <http://hackage.haskell.org/package/morte>

    Annah is a proof-of-concept library and does not provide several features
    like type-checking, evaluation, or pretty-printing.  Instead, Annah
    piggybacks on Morte; all Annah expressions are translated to Morte
    expressions and then those Morte expressions are type-checked and evaluated.

    Annah is not very user-friendly (and I apologize for that!).  For example,
    Annah reuses Morte's type-checker which means that error messages are in
    terms of low-level lambda calculus expressions and not in terms of the
    original Annah source code.
  
    This tutorial assumes that you have first read the Morte tutorial, which
    you can find here:

    <http://hackage.haskell.org/package/morte/docs/Morte-Tutorial.html>

    Annah is a superset of Morte that implements many of the higher-level
    constructs mentioned in the Morte tutorial, which is why you should not skip
    reading the Morte tutorial.
-}

module Annah.Tutorial (
    -- * Introduction
    -- $introduction

    -- * Let
    -- $let

    -- * Data types
    -- $datatypes

    -- * Imports
    -- $imports

    -- * Folds
    -- $folds
    ) where

{- $introduction
    This library comes with a binary executable that you can use to compile
    Annah expressions.  This executable can be used in two separate ways.

    First, you can read an Annah expression from standard input and the program
    will output the equivalent low-level Morte expression to standard output:

> $ annah
> type Bool
> data True
> data False
> fold if
> in                                                   
>     
> let not (b : Bool) : Bool = if b Bool False True
> in  not False
> <Ctrl-D>
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    Second, you can read an Annah expression in from a file if you provide the
    file name on the command line:

> $ cat example.annah
> type Bool
> data True
> data False
> fold if
> in                                                   
>     
> let not (b : Bool) : Bool = if b Bool False True
> in  not False
> $ annah example.annah
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    Annah is a superset of Morte, so any Morte expression is also a valid Annah
    expression:

> $ annah
> \(a : *) -> \(x : a) -> x
> <Ctrl-D>
> λ(a : *) → λ(x : a) → x

    Like Morte, Annah is an explicitly typed language (i.e. no type inference).
-}

{- $let
    Annah supports let expressions which can be used to introduce functions and
    values.  For example, this is how you can define the `id` function:

> $ annah
> let id (a : *) (x : a) : a = x
> in  id
> <Ctrl-D>
> λ(a : *) → λ(x : a) → x

    You can define more than one thing in a let expression as long as you
    prefix each definition with @let@:

> $ annah
> let id (a : *) (x : a) : a = x  
> let const (a : *) (b : *) (x : a) (y : b) : a = x
> in  id
> <Ctrl-D>
> λ(a : *) → λ(x : a) → x

    The general form of a @let@ expression is:

> let f0 (x00 : _A00) (x01 : _A01) ... (x0j : _A0j) _B0 = b0
> let f1 (x10 : _A10) (x11 : _A11) ... (x1j : _A1j) _B1 = b1
> ...
> let fi (xi0 : _Ai0) (xi1 : _Ai1) ... (xij : _Aij) _Bi = bi
> in  e

    The above let expression desugars to the following lambda expression:

> (   λ(f0 : ∀(x00 : _A00) → ∀(x01 : _A01) → ... → ∀(x0j : _A0j) → _B0)
> →   λ(f1 : ∀(x10 : _A10) → ∀(x11 : _A11) → ... → ∀(x1j : _A1j) → _B1)
> →   ...
> →   λ(fi : ∀(xi0 : _Ai0) → ∀(xi1 : _Ai1) → ... → ∀(xij : _Aij) → _Bi)
> →   e
> )
> 
> (λ(x00 : _A00) → λ(x01 : _A01) → ... → λ(x0j : _A0j) → b0)
> (λ(x10 : _A10) → λ(x11 : _A11) → ... → λ(x1j : _A1j) → b1)
> ...
> (λ(xi0 : _Ai0) → λ(xi1 : _Ai1) → ... → λ(xij : _Aij) → bi)

    The above @\'e\'@  is the \"body\" of the let expression and @f0@ through
    @fi@ are the \"let-bound terms\".  Due to the above translation, each
    \"let-bound\" term is only in scope for the \"body\" of the let-expression
    and the types of subsequent \"let-bound\" terms.

    To give a concrete example, our original @id@+@const@ let expression:

> let id (a : *) (x : a) : a = x  
> let const (a : *) (b : *) (x : a) (y : b) : a = x
> in  id

    ... was equivalent to:

> (   λ(id : ∀(a : *) → ∀(x : a) → a)
> →   λ(const : ∀(a : *) → ∀(b : *) → ∀(x : a) → ∀(y : b) → a
> →   id
> )
>
> (λ(a : *) → λ(x : a) → x)
> (λ(a : *) → λ(b : *) → λ(x : a) → λ(y : b) → x)

    ... which normalizes to:

> λ(a : *) → λ(x : a) → x

    The definition of @const@ is dead code that is optimized away by β-reduction
    because the let-bound @const@ term is never used within the body of the let
    expression.
-}

{- $datatypes
    Annah lets you define datatypes that scope over an expression.  For example,
    if you write:

> type Bool
> data True
> data False
> fold if
> in e

    ... then within the expression @\'e\'@ you will be able to use the @Bool@
    type, the @True@ and @False@ values, and the @if@ fold.

    The above definition of @Bool@ desugars to the following @let@ expression:

> let Bool  : *    = ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> let True  : Bool = λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True
> let False : Bool = λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False
> let if : Bool → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool =
>     λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x
> in  e

    ... which in turn desugars to:

> (   λ(Bool : *)
> →   λ(True : Bool)
> →   λ(False : Bool)
> →   λ(if : Bool → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool)
> →   e
> )
> 
> (∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool)
> (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True)
> (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False)
> (λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x)

    Annah also supports recursive data types.  For example, you can define
    natural numbers like this:

> $ annah
> type Nat
> data Succ (pred : Nat)
> data Zero
> in   Succ (Succ (Succ Zero))
> <Ctrl-D>
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    Notice how we can omit the @fold@ line, which is optional.

    You can also omit field names, too, and this code is also valid:

> $ annah
> type Nat
> data Succ Nat
> data Zero
> in   Succ (Succ (Succ Zero))
> λ(Nat : *) → λ(Succ : Nat → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    Field names are just used to give nicer names to bound variables in the
    desugared datatype definition and field names default to @\'_\'@ if you omit
    the name.

    You can find out how any given type or constructor is encoded by just
    returning the constructor as the result of the let expression:

> $ annah
> type Nat
> data Succ (pred : Nat)
> data Zero
> in   Succ
> λ(pred : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (pred Nat Succ Zero)

-}

{- $imports
    Annah supports imports using the same syntax as Morte but you may only
    import Morte expressions (**not** Annah expressions).  You can embed a
    file path or http URL anywhere within an expression and Annah will
    substitute in the plain-text Morte expression located at that path or URL.

    The reason Annah does not support importing Annah expressions is that Annah
    does not actually resolve the imports.  Annah piggybacks off of Morte's
    support for imports, and Morte only supports importing Morte expressions.

    Imports are extremely useful when combined with data types because you can
    create a separate file for each type and constructor of a data type.  To
    illustrate this we'll encode @Bool@, @True@, @False@, and @if@ as separate
    Annah files:

> $ cat Bool.annah
> type Bool
> data True
> data False
> fold if
> in   Bool

> $ cat True.annah
> type Bool
> data True
> data False
> fold if
> in   True

> $ cat False.annah
> type Bool
> data True
> data False
> fold if
> in   False

> $ cat if.annah
> type Bool
> data True
> data False
> fold if
> in   if

    Then we will translate each of them to a file encoding the equivalent Morte
    expression without the @\".annah\"@ file suffix:

> $ annah  Bool.annah > Bool
> $ annah  True.annah > True
> $ annah False.annah > False
> $ annah    if.annah > if

    Now that we've created a file for each type and term we can import them
    within other expressions.  For example, now we can define the @not@ function
    in terms of imported types and values:

> $ cat not.annah
> let not (b : ./Bool ) : ./Bool = ./if b ./Bool ./False ./True
> in  not

    Don't worry if you don't understand what the above expression means just
    yet.  This tutorial will explain what the right-hand side means in the
    section on \"Folds\".

    We can run this file through Annah, which will desugar and normalize the
    expression, but will preserve the original imports:

> $ annah not.annah > not
> $ cat not
> λ(b : ./Bool ) → ./if  b ./Bool  ./False  ./True

    Annah actually does resolve the imports for the purposes of type-checking
    the expression, but deliberately does not resolve the imports for the final
    normalized expression.  Annah does this to keep the expression \"dynamically
    linked\" so that the expression can continue to reflect changes to
    dependencies.

    If you prefer to statically link the expression then you can use Morte:

> $ echo "./not" | morte
> ∀(b : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(b : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → b (∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False) (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True)

    ... and you can also expand derived expressions, too:

> $ morte
> ./not ./True
> <Ctrl-D>
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False

    ... desugaring them with Annah if necessary:

> $ annah | morte
> let doubleNegate (b : ./Bool ) : /Bool = ./not (./not b)
> in  doubleNegate ./True
> <Ctrl-D>
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
>
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

-}

{- $folds
    Every datatype definition comes with an optional @fold@.  This fold lets you
    pattern match on the type to obtain the result.  You can see what arguments
    the pattern match expects just by querying the type of the fold:

> $ annah | morte
> type Bool
> data True
> data False
> fold if
> in   if
> <Ctrl-D>
> ∀(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x

    ... and we can simplify the type to:

> ∀(x : ./Bool ) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

    This type says that @if@ expects the following arguments:

* A value of type @./Bool@ to pattern match on (such as @./True@ or @./False@)
* The type of the result
* The result to return if our value equals @./True@
* The result to return if our value equals @./False@

    Carefully note that the second argument is named @Bool@ but can actually be
    any type.  Similarly, the third and fourth arguments are named after the
    @True@ and @False@ constructors but they actually represent how to handle
    each branch of the pattern match.

    So, for example, when we write:

> let not (b : ./Bool ) : ./Bool = ./if b ./Bool ./False ./True
> in  not

    ... it's as if we wrote the following Haskell code using pattern matching:

> let not :: Bool -> Bool
>     not b = case b of
>             True  -> False
>             False -> True
> in  not

    We could even format our code to parallel the layout of a Haskell pattern
    match:

> let not (b : ./Bool ) : ./Bool =
>     ./if b ./Bool
>     ./False
>     ./True
> in  not

    The only difference is that in the Annah code we have to explicitly supply
    the expected type of the result after the value that we pattern match on
    (i.e. the @./Bool@ immediately after the @./if b@).

    Our @./not@ function technically did not really need to use the @./if@
    @fold@.  For example, we could instead write:

> $ cat not.annah
> let not (b : ./Bool ) : ./Bool = b ./Bool ./False ./True
> in  not

    The @./if@ was unnecessary because it was just the identity function on
    @./Bool@s:

> $ cat if
> λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x

    .. which is the same as:

> λ(x : ./Bool ) → x

    The reason this works is that all values of type @./Bool@ are already
    preformed pattern matches.  We can prove this to ourselves by consulting
    the definitions of @./True@ and @./False@:

> $ morte < ./True
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True
> $ morte < ./False
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False

    In other words, @./True@ is just a preformed pattern match that always
    returns the first branch that you supply.  Vice versa, @./False@ is just a
    preformed pattern match that always returns the second branch that you
    supply.

    In fact, all @fold@s are optional when you save a type and associated data
    constructors as separate files.  The only time we truly require the @fold@
    is when we pattern match on the type within the "body" of a data type
    expression, like in our very first example:

> type Bool
> data True
> data False
> fold if
> in -- Everything below here is the "body" of the `Bool` data type definition
>
> let not (b : Bool) : Bool = if b Bool False True
> in  not False

    @Bool@ and @./Bool@ are not the same type within the "body" of the @Bool@
    data type definition.  If you omit the @if@ then you will get the following
    type error:

> $ annah
> type Bool
> data True
> data False
> fold if
> in
> 
> let not (b : Bool) : Bool = b Bool False True
> in  not False
> <Ctrl-D>
> annah: 
> Context:
> Bool : *
> True : Bool
> False : Bool
> if : ∀(x : Bool) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> b : Bool
> 
> Expression: b Bool
> 
> Error: Only functions may be applied to values

    The @Context@ the compiler prints in the error message shows that the
    type-checker views the @Bool@ type as abstract and not the type of a
    pattern match.  However, the same @Context@ says that @if@ has the correct
    type to convert between the abstract @Bool@ type and the type we expect for
    a pattern match:

> if : ∀(x : Bool) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

    ... which we can simplify to just:

> -- The type of the bound variable named `if`
> if : ∀(x : Bool) → ./Bool

    In other words, @Bool@ and @./Bool@ are different types from the type
    checker's point of view.  That is why you must explicitly convert from
    @Bool@ to @./Bool@ using @if@ while inside that context.

    However, once you save @./Bool@, @./True@, @./False@ and @./if@ to separate
    files the distinction between @Bool@ and @./Bool@ vanishes.  The type of
    @./if@ (the file) is not the same as the type as @if@ (the bound variable):

> -- The type of the file named `./if`
> ./if : ./Bool → ./Bool

    You can deduce why the distinction disappears when you save things to
    separate files if you desugar the data type definitions.  For example our
    @if.annah@ file was defined as:

> type Bool
> data True
> data False
> fold if
> in   if

    ... which desugars to:

> (   λ(Bool : *)
> →   λ(True : Bool)
> →   λ(False : Bool)
> →   λ(if : Bool → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool)
> →   if
> )
> 
> (∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool)
> (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True)
> (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False)
> (λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x)

    ... and then normalizes to;

> $ morte < if
> ∀(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x

    There is also another use for storing @fold@s as files and using them, even
    if they are not immediately necessary.  Saving a @fold@ to a file lets you
    provide a stable interface for pattern matching on a value if you ever
    want to change the internal implementation of a type without breaking
    backwards compatibility.

    For example, suppose that a user writes the following @not@ function using
    @./if@:

> let not (b : ./Bool ) : ./Bool = ./if b ./Bool ./False ./True
> in  not

    ... but we later decide we want to flip the order of of the @True@ and
    @False@ constructors in our datatype definition:

> $ annah > Bool
> type Bool
> data False
> data True
> in   Bool
> $ annah > True
> type Bool
> data False
> data True
> in   True
> $ annah > False
> type Bool
> data False
> data True
> in   False

    The above changes would break the user's code unless we change @./if@ to
    export the pattern match order that the user expects:

> $ cat if
>     \(b : ./Bool )
> ->  \(Bool : *)
> ->  \(True : Bool)
> ->  \(False : Bool)
> ->  b Bool False True

    Now the user's code continues to work as if nothing ever happened.

    Therefore, saving @fold@s to files and using them to pattern match is not
    necessary, but if you do use them then you can change the underlying
    implementation of the type without breaking backwards compatibility.

    There's no way that you can force users to use the @fold@ that you provide
    since all saved expressions are encoded in raw lambda calculus, which does
    not provide any support for implementation hiding or encapsulation.  The
    best you can do is to simply warn users that you might break their code some
    day if they perform a \"raw pattern match\" (i.e. a pattern match without
    the use of a saved @fold@).
-}
