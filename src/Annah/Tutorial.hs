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

    -- * Recursive types
    -- $recursive

    -- * Prelude
    -- $prelude

    -- * Standard library
    -- $stdlib
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

> $ annah  Bool.annah >  Bool
> $ annah  True.annah >  True
> $ annah False.annah > False
> $ annah    if.annah >    if

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

    * A value of type @./Bool@ to pattern match on (such as @./True@ or
      @./False@)
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
> <Ctrl-D>
> $ annah > True
> type Bool
> data False
> data True
> in   True
> <Ctrl-D>
> $ annah > False
> type Bool
> data False
> data True
> in   False
> <Ctrl-D>

    The above changes would break the user's code unless we change @./if@ to
    export the pattern match order that the user expects:

> $ echo > if
>     \(b : ./Bool )
> ->  \(Bool : *)
> ->  \(True : Bool)
> ->  \(False : Bool)
> ->  b Bool False True
> <Ctrl-D>

    Now the user's code continues to work as if nothing ever happened.

    So saving @fold@s to files and using them to pattern match is not strictly
    necessary, but if you do use them then you can change the underlying
    implementation of the type without breaking backwards compatibility.

    There's no way that you can force users to use the @fold@ that you provide
    since all saved expressions are encoded in lambda calculus, which does not
    provide any support for implementation hiding or encapsulation.  The best
    you can do is to simply warn users that you might break their code some
    day if they perform a \"raw pattern match\" (i.e. a pattern match without
    the use of a saved @fold@).
-}

{- $recursive
    Annah supports recursive and mutually recursive types.  We saw an example
    of recursive types with natural numbers:

> $ annah
> type Nat
> data Succ (pred : Nat)
> data Zero
> fold foldNat
>
> in   Succ (Succ (Succ Zero))
> <Ctrl-D>
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    What might not be obvious is that if you save each type and constructor to
    a separate file then you can build a natural number just from the files.

    First, we will save each type and term to a separate @*.annah@ file:

> $ cat Nat.annah
> type Nat
> data Succ (pred : Nat)
> data Zero
> fold foldNat
> in   Nat

> $ cat Succ.annah
> type Nat
> data Succ (pred : Nat)
> data Zero
> fold foldNat
> in   Succ

> $ cat Zero.annah
> type Nat
> data Succ (pred : Nat)
> data Zero
> fold foldNat
> in   Zero

> $ cat foldNat.annah
> type Nat
> data Succ (pred : Nat)
> data Zero
> fold foldNat
> in   foldNat

    Then we will compile them to Morte code that we can import:

> $ annah    Bool.annah >    Bool
> $ annah    Succ.annah >    Succ
> $ annah    Zero.annah >    Zero
> $ annah foldNat.annah > foldNat

    ... and now we can build natural numbers directly without having to first
    introduce a natural number datatype definition:

> $ morte
> ./Succ (./Succ (./Succ ./Zero ))
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    This gives the exact same result as before, but now we are programming
    directly at the "top level" using files instead of programming underneath
    a datatype definition.

    Also notice that the inferred type of our expression is identical to
    @./Nat@:

> $ cat ./Nat
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat

    We can also fold natural numbers using our @./foldNat@ function.  Let's
    consult the type of the function:

> ∀(x : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(x : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → x

    If we clean up that type we get:

>     ∀(x : ./Nat )
> →   ∀(Nat : *)
> →   ∀(Succ : ∀(pred : Nat) → Nat)
> →   ∀(Zero : Nat)
> →   Nat

    Conceptually, when we fold a @./Nat@ value using @./foldNat@ we just
    replace each @Succ@ constructor with the argument of the fold labeled @Succ@
    (i.e. the third argument).  Similarly, we substitute each @Zero@ constructor
    with the fourth argument.

    We also supply a type parameter named @Nat@ as the second argument.  This
    type parameter must match the input and output of whatever we use to replace
    the @Succ@ and @Zero@.

    For example, suppose that we wanted to write a function to test if a @./Nat@
    was an even number.  We would just substitute every @Zero@ constructor with
    @./True@ and substitute every @Succ@ constructor with @./not@.  The code
    for that would be:

> $ cat isEven.annah 
> let isEven (n : ./Nat ) : ./Bool =
>     ./foldNat n ./Bool
>         ./not  -- Replace every `Succ` with `./not`
>         ./True -- Replace every `Zero` with `./True`
> in  isEven

    The let definition is not strictly necessary since we could just write:

> \(n : ./Nat ) ->
>     ./foldNat n ./Bool
>         ./not
>         ./True

    ... but the let definition helps the readability of the code by naming the
    function and documenting the expected return type.

    Then we can compile our Annah expression to Morte code:

> $ annah isEven.annah > isEven

    ... and test that @./isEven@ works:

> $ morte
> ./isEven (./Succ (./Succ ./Zero ))
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    It works!  The result is identical to @./True@:

> $ cat ./True
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    Conceptually, what happened was that @./isEven@ just performed the
    desired substitutions, replacing every @./Succ@ with @./not@ and replacing
    every @./Zero@ with @./True@:

> ./isEven (./Succ (./Succ ./Zero ))
>
> -- Constructor substitution
> = ./not (./not ./True )
>
> -- β-reduce
> = ./True

    Note that this is not the path the compiler takes under the hood, but it's
    equivalent.

    We can also encode mutually recursive types such as the following type
    declaration for even and odd numbers:

> $ annah
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in SuccE (SuccO ZeroE)
> λ(Even : *) → λ(Odd : *) → λ(SuccE : ∀(predE : Odd) → Even) → λ(ZeroE : Even) → λ(SuccO : ∀(predO : Even) → Odd) → SuccE (SuccO ZeroE)

    Like before, we can encode each type and term separately as files and the
    files:

> $ cat Even.annah 
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in   Even

> $ cat SuccE.annah 
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in   SuccE

> $ cat ZeroE.annah 
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in   ZeroE

> $ cat foldEven.annah 
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in   foldEven

> $ cat Odd.annah 
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in   Odd

> $ cat SuccO.annah 
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in   SuccO

> $ cat foldOdd.annah 
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> 
> in   foldOdd

    ... convert them to Morte code:

> $ annah     Even.annah >     Even
> $ annah    ZeroE.annah >    ZeroE
> $ annah    SuccE.annah >    SuccE
> $ annah foldEven.annah > foldEven
> $ annah      Odd.annah >      Odd
> $ annah    SuccO.annah >    SuccO
> $ annah  foldOdd.annah >  foldOdd

    ... and now these files can be used to build @./Even@ or @./Odd@ values:

> $ morte
> ./SuccE (./SuccO ./ZeroE )
> <Ctrl-D>
> ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even
> 
> λ(Even : *) → λ(Odd : *) → λ(SuccE : ∀(predE : Odd) → Even) → λ(ZeroE : Even) → λ(SuccO : ∀(predO : Even) → Odd) → SuccE (SuccO ZeroE)

    We can also consume mutually recursive types just by folding them.  Each
    type is already a preformed fold and we can consult each type's respective
    @fold@ function to see what arguments the @fold@ expects:

> $ morte < foldEven
> ∀(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even) → ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even
> 
> λ(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even) → x
> $ morte < foldOdd
> ∀(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Odd) → ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Odd
> 
> λ(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Odd) → x

    If we clean up the type of the @./foldEven@ function we get this:

>     ∀(x : ./Even )
> →   ∀(Even : *)
> →   ∀(Odd : *)
> →   ∀(SuccE : ∀(predE : Odd) → Even)
> →   ∀(ZeroE : Even)
> →   ∀(SuccO : ∀(predO : Even) → Odd)
> →   Even

    Conceptually, when we fold an @./Even@ value using @./foldEven@ we just
    replace each @SuccE@ constructor with the argument of the fold labeled
    @SuccE@ (i.e. the fourth argument).  Similarly, we substitute each @ZeroE@
    constructor with the fifth argument named @ZeroE@ and substitute each
    @SuccO@ constructor with the sixth argument named @SuccO@.

    We also supply two type parameters named @Even@ and @Odd@.  These type
    parameters must match the input and output of whatever we use to replace
    the @SuccE@, @ZeroE@ and @SuccO@ constructors.

    For example, suppose that we wanted to write a function that converts an
    @./Even@ value to a @./Nat@.  We would just replace every @SuccE@ and
    @SuccO@ constructor with @Succ@ and replace every @ZeroE@ constructor with
    @Zero@, like this:

> $ cat evenToNat.annah
> let evenToNat (e : ./Even ) : ./Nat =
>     ./foldEven e ./Nat ./Nat
>     ./Succ  -- Replace every `SuccE` with `Succ`
>     ./Zero  -- Replace every `ZeroE` with `Zero`
>     ./Succ  -- Replace every `SuccO` with `Succ`
> in  evenToNat

    Now we can \"compile\" our @evenToNat@ function to Morte code:

> annah evenToNat.annah > evenToNat

    ... and test that it correctly converts @./Even@ values to their
    equivalent @./Nat@ values:

> $ morte
> ./evenToNat (./SuccE (./SuccO ./ZeroE ))
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ Zero)

    It works!  We can began with the number two, encoded as an @./Even@ number
    and ended with two encoded as a @./Nat@.

    As before, the @./evenTonat@ function was just performing the desired
    substitution, replacing each @./SuccE@ and @./SuccO@ with @./Succ@ and
    replacing @./ZeroE@ with @./Zero@:

> ./evenToNat (./SuccE (./SuccO ./ZeroE ))
>
> -- Constructor substitution
> = ./Succ (./Succ ./Zero )
>
> -- β-reduction
> = ./Succ (./Succ ./Zero )

    Again, this is not the path the compiler takes under the hood, but it's
    equivalent.
-}

{- $prelude
    Annah also comes with a Prelude of utility types and terms.  This Prelude is
    hosted remotely here:

    <http://sigil.place/tutorial/annah/1.0/>

    You can visit the above link to browse the Prelude and see what is
    available.

    There are several ways that you can use the Prelude.  The most direct
    approach is to use expressions from the Prelude directly by referencing
    their URLs, like this:

> $ morte
> http://sigil.place/tutorial/annah/1.0/Nat/Succ
> (   http://sigil.place/tutorial/annah/1.0/Nat/Succ
>     (   http://sigil.place/tutorial/annah/1.0/Nat/Succ
>         http://sigil.place/tutorial/annah/1.0/Nat/Zero
>     )
> )
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    ... or you can selectively \"alias\" remote references locally by creating
    local files that refer to the remote URLs:

> $ echo "http://sigil.place/tutorial/annah/1.0/Nat/Succ" > Succ
> $ echo "http://sigil.place/tutorial/annah/1.0/Nat/Zero" > Zero
> $ morte
> ./Succ (./Succ (./Succ ./Zero ))
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    ... or you can \"import\" the entire Prelude into your current directory
    using @wget@:

> $ wget -np -nH -r --cut-dirs=3 http://sigil.place/tutorial/annah/1.0/
> $ ls
> (->)            Defer.annah    List.annah    Path         Sum0.annah
> (->).annah      Eq             Maybe         Path.annah   Sum1
> Bool            Eq.annah       Maybe.annah   Prod0        Sum1.annah
> Bool.annah      Functor        Monad         Prod0.annah  Sum2
> Category        Functor.annah  Monad.annah   Prod1        Sum2.annah
> Category.annah  index.html     Monoid        Prod1.annah
> Cmd             IO             Monoid.annah  Prod2
> Cmd.annah       IO.annah       Nat           Prod2.annah
> Defer           List           Nat.annah     Sum0

    This tutorial will assume that you have imported the Prelude locally.

    The Prelude is organized according to the following rules:

    * Each type (like @Bool@ or @Nat@ is a top-level directory.  You can
      reference that type in your code by its directory
    * Each constructor of that type lives underneath the type's directory.  For
      example, @True@ is located underneath the @Bool@ directory
    * Functions associated with each type are also located underneath the type's
      directory.  For example, the @length@ function is located underneath the
      @List@ directory.
    * Every expression is provided as both the original Annah code (with a
      @*.annah@ suffix) and Morte code (with no suffix).  For example, you
      will find the @Monoid.annah@ file which was the Annah expression used to
      create the @Monoid@ file which is a Morte expression.

    In order to use an expression within Morte you must explicitly import the
    expression within the Morte code, like this:

> $ echo "./List/length" | morte  # Good
> ∀(a : *) → ∀(xs : ∀(List : *) → ∀(Cons : ∀(head : a) → ∀(tail : List) → List) → ∀(Nil : List) → List) → ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Nil : Nat) → Nat
> 
> λ(a : *) → λ(xs : ∀(List : *) → ∀(Cons : ∀(head : a) → ∀(tail : List) → List) → ∀(Nil : List) → List) → λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → xs Nat (λ(_ : a) → Succ)

    Reading the expression through standard input will (usually) not work:

> $ morte < List/length  # Bad
> ../List: openFile: does not exist (No such file or directory)

    The reason why is that everything in the Prelude uses relative imports to
    reference each other.  This is what allows the Prelude to correctly
    function both when you reference the Prelude remotely and when you download
    the Prelude locally.  If you read the expression through standard input
    then Morte incorrectly concludes that any further imports are relative to
    your current directory.  However, if you explicitly import the expression
    within the code then Morte correctly concludes that transitive imports are
    relative to the imported file's path.

    For example, the @List/length@ file has the following contents:

> cat List/length
> λ(a : *) → λ(xs : ../List  a) → λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → xs Nat (λ(_ : a) → Succ)

    There is one relative reference within that file to @../List@.  That
    reference is relative to the current file's directory (i.e. relative to
    @List/@) which means that it still points to the same directory: @List@.  We
    could have also used just @.@ to refer to the current directory but that
    would be less readable.  However, if you read in @List/length@ from standard
    input, then @morte@ looks for @../List@ expression relative to your present
    working directory and fails.
-}

{- $stdlib
    Annah's Prelude has some similarities to Haskell's standard libraries and
    some differences.  The rough correspondences are:

    * @(->)@ corresponds to Haskell's @(->)@ type constructor
    * @Bool@ corresponds to Haskell's `Bool` type
    * @Cmd@ corresponds to the operational monad (i.e.
      "Control.Monad.Operational".`Control.Monad.Operational.Program`
    * @Defer@ corresponds to
      "Data.Functor.Coyoneda".`Data.Functor.Coyoneda.Coyoneda`
    * @IO@ corresponds to a very simple `IO` type constructor that only supports
      two operations:

        > ./IO/get : ./IO ./Nat
        > ./IO/put : ./Nat -> ./IO ./Prod0
    * @List@ corresponds to Haskell lists except that Annah @List@s are always
      finite because they are encoded recursively
    * @Maybe@ corresponds to Haskell's `Maybe` type constructor
    * @Nat@ corresponds to Haskell's `Numeric.Natural.Natural` type, except
      much less efficient than its Haskell counterpart
    * @Path@ corresponds to a free category.  As far as I know there is no
      standard Haskell implementation for free categories to reference
    * @Prod0@ corresponds to Haskell's @()@ type.  Mnemonic: \"Product type with
      zero fields\"
    * @Prod1@ corresponds to Haskell's `Data.Functor.Identity` type constructor.
      Mnemonic: \"Product type with one field\"
    * @Prod2@ corresponds to Haskell's 2-tuple type constructor.  Mnemonic:
      \"Product type with two fields\"
    * @Sum0@ corresponds to Haskell's `Data.Void.Void` type.  Mnemonic: \"Sum
      type with zero fields\"
    * @Sum1@ also corresponds to Haskell's `Data.Functor.Identity` type
      constructor.  Mnemonic: \"Sum type with one field\"
    * @Sum2@ corresponds to Haskell's `Either` type constructor.  Mnemonic:
      \"Sum type with two fields\"

    In addition to those types, Annah also encodes several of Haskell's type
    classes as values.  Neither Annah nor Morte supports type classes /per se/.
    Instead, each class is encoded as a type constructor and each instance is
    a term of the corresponding type.
-}
