{-| Annah is a tiny language that serves to illustrate how various programming
    constructs can be desugared to lambda calculus.  The most sophisticated
    feature that Annah supports is desugaring mutually recursive datatypes
    to non-recursive lambda expressions.

    Annah is not intended to be used as a production language.  Rather, Annah is
    a step along the way towards a production language that I factored out as
    a reusable library that others can learn from and possibly fork for their
    own use cases.

    Under the hood, all Annah expressions are translated to a minimalist
    implementation of the calculus of constructions called Morte, which only
    supports non-recursive lambda expressions and their types.  You can find
    the Morte compiler and library here:

    <http://hackage.haskell.org/package/morte>

    Annah piggybacks on Morte meaning all Annah expressions are translated to
    Morte expressions and then those Morte expressions are type-checked and
    evaluated.  You cannot directly type-check or evaluate Annah expressions;
    you have to desugar them to Morte expressions first before you can do
    anything else with them.

    Annah is not very user-friendly (and I apologize for that!).  For example,
    Annah reuses Morte's type-checker which means that error messages are in
    terms of low-level lambda calculus expressions and not in terms of the
    original Annah source code.
  
    Most notably, Annah does not provide support for text, due to the gross
    inefficiency of encoding even basic ASCII text in lambda calculus.  Text
    handling would be better served by a backend with primitive support for
    text literals and operations on text.

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

    -- * Autogenerate Types
    -- $types

    -- * Folds
    -- $folds

    -- * Recursive types
    -- $recursive

    -- * Prelude
    -- $prelude

    -- * Natural numbers
    -- $nats

    -- * Lists
    -- $lists

    -- * Monoids
    -- $monoids

    -- * Commands
    -- $commands

    -- * IO
    -- $io

    -- * Paths
    -- $paths
    ) where

{- $introduction
    This library comes with a binary executable that you can use to compile
    Annah expressions to Morte expressions.  This executable can be used in two
    separate ways.

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
    file name on the command line using the @compile@ subcommand:

> $ cat example.annah
> type Bool
> data True
> data False
> fold if
> in                                                   
>     
> let not (b : Bool) : Bool = if b Bool False True
> in  not False

> $ annah compile example.annah
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
    values.  For example, this is how you can define the polymorphic identity
    function in Annah:

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

    Annah also supports recursive datatypes.  For example, you can define
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
    import Morte expressions (/not/ Annah expressions).  You can embed a file
    path or http URL anywhere within an expression and Annah will substitute in
    the Morte expression (encoded as plain text) located at that path or URL.

    The reason Annah does not support importing Annah expressions is that Annah
    does not actually resolve the imports.  Annah piggybacks off of Morte's
    support for imports, and Morte only supports importing Morte expressions.

    Imports are extremely useful when combined with datatypes because you can
    create a separate file for each type and constructor of a datatype.  To
    illustrate this we'll manually encode @Bool@, @True@, @False@, and @if@ as
    separate Annah files (and later we will see how we can auto-generate these
    files):

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

> $ annah compile  Bool.annah >  Bool
> $ annah compile  True.annah >  True
> $ annah compile False.annah > False
> $ annah compile    if.annah >    if

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

> $ annah compile not.annah > not
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

{- $types
    Creating one file per type, fold, and data constructor gets tedious pretty
    quickly, so the @annah@ executable provides a convenient subcommand named
    @types@ for auto-generating these files.

    Just run the @annah types@ command and provide a datatype definition on
    standard input:

> $ annah types
> type Bool
> data True
> data False
> fold if
> <Ctrl-D>

    ... and @annah@ will create one directory for each type in the datatype
    definition:

> $ ls
> Bool/  Bool.annah

    Each type's directory will have two files per data constructor associated
    with the type and two files for the @fold@, too:

> $ ls Bool
> @  False  False.annah  if  if.annah  True  True.annah

    Everything comes in two flavors: the original Annah code and the equivalent
    Morte code:

> $ cat Bool/True.annah 
> type Bool
> data True
> data False
> fold if
> in   True
> $ cat Bool/True
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    The Morte code for the type is located as a file named @\@@ underneath the
    type's directory:

> $ cat Bool.annah
> type Bool
> data True
> data False
> fold if
> in   Bool
> $ cat Bool/@
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

    This is because Morte supports importing the directory by name if there is a
    file named @\@@ underneath the directory.  So, for example if you import
    @./Bool@ and it's a directory then Morte will import @.\/Bool\/\@@ instead:

> $ morte
> ./Bool
> <Ctrl-D>
> *
> 
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
-}

{- $folds
    Every datatype definition comes with an optional @fold@ which you can use to
    pattern match on a value of that type.  You can see what arguments the
    pattern match expects just by querying the type of the fold:

> $ morte
> ./Bool/if
> <Ctrl-D>
> ∀(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x

    ... and we can use imports to simplify the type to:

> ∀(x : ./Bool ) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

    This type says that @if@ expects the following arguments:

    * A value named @x@ of type @./Bool@ to pattern match on (like
      @.\/Bool\/True@ or @.\/Bool\/False@)
    * The type of the result for each branch of the pattern match
    * The result to return if our value equals @.\/Bool\/True@
    * The result to return if our value equals @.\/Bool\/False@

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

    Our @./not@ function technically did not need to use the @./if@ @fold@.  For
    example, we could instead write:

> $ cat not.annah
> let not (b : ./Bool ) : ./Bool = b ./Bool ./False ./True
> in  not

    The @./if@ was unnecessary because it was just the identity function on
    @./Bool@s:

> $ cat if
> λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x

    .. which is the same as:

> λ(x : ./Bool ) → x

    The reason we can omit the @if@ is that all values of type @./Bool@ are
    already preformed pattern matches.  We can prove this to ourselves by
    consulting the definitions of @.\/Bool\/True@ and @.\/Bool\/False@:

> $ morte < ./Bool/True
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True
> $ morte < ./Bool/False
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False

    In other words, @.\/Bool\/True@ is just a preformed pattern match that
    always returns the first branch that you supply.  Vice versa,
    @.\/Bool\/False@ is just a preformed pattern match that always returns the
    second branch that you supply.

    In fact, all @fold@s are optional when you save a type and associated data
    constructors as separate files.  The only time we truly require the @fold@
    is when we pattern match on the type within the "body" of a datatype
    expression, like in our very first example:

> type Bool
> data True
> data False
> fold if
> in -- Everything below here is the "body" of the `Bool` datatype definition
>
> let not (b : Bool) : Bool = if b Bool False True
> in  not False

    @Bool@ and @./Bool@ are not the same type within the "body" of the @Bool@
    datatype definition.  If you omit the @if@ then you will get the following
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
    @./if@ (the file) is not the same as the type of @if@ (the bound variable):

> -- The type of the file named `./if`
> ./if : ∀(x : ./Bool ) → ./Bool

    You can deduce why the distinction disappears when you save things to
    separate files if you desugar the datatype definitions.  For example our
    @if.annah@ file was defined as:

> type Bool
> data True
> data False
> fold if
> in   if

    We can use the @annah desugar@ subcommand to see what that code desugars to
    before normalization:

> $ annah desugar < ./Bool/if.annah
> (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → λ(if : ∀(x : Bool) → ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → if) (∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True) (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False) (λ(x : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → x)

    ... which we can clean up a bit to get:

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

    That then normalizes to;

> $ annah desugar < ./Bool/if.annah | morte
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

> $ annah types
> type Bool
> data False
> data True

    The above changes would break the user's code unless we change @./if@ to
    export the pattern match order that the user expects:

> $ cat > if
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

    To illustrate this, we will compile our datatype definition to separate
    files:

> $ annah types
> type Nat
> data Succ (pred : Nat)
> data Zero
> fold foldNat
> <Ctrl-D>

    ... and now we can build natural numbers using these files:

> $ morte
> ./Nat/Succ (./Nat/Succ (./Nat/Succ ./Nat/Zero ))
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    This gives the exact same result as before, but now we are programming
    directly at the "top level" using files instead of programming inside the
    body of a datatype definition.

    We can also fold natural numbers using our @.\/Nat\/foldNat@ function.
    Let's consult the type of the function:

> ∀(x : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(x : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → x

    If we clean up that type we get:

>     ∀(x : ./Nat )
> →   ∀(Nat : *)
> →   ∀(Succ : ∀(pred : Nat) → Nat)
> →   ∀(Zero : Nat)
> →   Nat

    Conceptually, when we fold a @./Nat@ value using @.\/Nat\/foldNat@ we just
    replace each @.\/Nat\/Succ@ constructor with the argument of the fold
    labeled @Succ@ (i.e. the third argument).  Similarly, we substitute each
    @.\/Nat\/Zero@ constructor with the fourth argument labeled @Zero@.

    We also supply a type parameter named @Nat@ as the second argument.  This
    type parameter must match the input and output of whatever we use to replace
    the @.\/Nat\/Succ@ and @.\/Nat\/Zero@.

    For example, suppose that we wanted to write a function to test if a @./Nat@
    was an even number.  We would just substitute every @Zero@ constructor with
    @.\/Bool\/True@ and substitute every @.\/Nat\/Succ@ constructor with
    @./not@.  The code for that would be:

> $ cat not.annah  # Update `not.annah` to use our new file layout
> let not (b : ./Bool ) : ./Bool =
>     ./Bool/if b ./Bool
>         ./Bool/False
>         ./Bool/True
> in  not

> $ cat isEven.annah 
> let isEven (n : ./Nat ) : ./Bool =
>     ./Nat/foldNat n ./Bool
>         ./not       -- Replace every `./Nat/Succ` with `./not`
>         ./Bool/True -- Replace every `./Nat/Zero` with `./Bool/True`
> in  isEven

    The let definitions are not strictly necessary since we could just write:

> $ cat not.annah
> \(b : ./Bool ) ->
>     ./Bool/if b ./Bool
>         ./Bool/False
>         ./Bool/True

> $ cat isEven.annah
> \(n : ./Nat ) ->
>     ./Nat/foldNat n ./Bool
>         ./not
>         ./Bool/True

    ... but the let definitions help the readability of the code by naming the
    functions and documenting their expected return types.

    Then we can compile our Annah expression to Morte code:

> $ annah compile    not.annah > not
> $ annah compile isEven.annah > isEven

    ... and test that @./isEven@ works:

> $ morte
> ./isEven (./Nat/Succ (./Nat/Succ ./Nat/Zero ))
> <Ctrl-D>
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    It works!  The result is identical to @.\/Bool\/True@:

> $ morte
> ./Bool/True
> <Ctrl-D>
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
>
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    Conceptually, what happened was that @./isEven@ just performed the
    desired substitutions, replacing every @.\/Nat\/Succ@ with @./not@ and
    replacing every @.\/Nat\/Zero@ with @.\/Bool\/True@:

> ./isEven (./Nat/Succ (./Nat/Succ ./Nat/Zero ))
>
> -- Constructor substitution
> = ./not (./not ./Bool/True )
>
> -- β-reduce
> = ./Bool/True

    Note that this is not really the path the compiler takes under the hood, but
    it's equivalent.

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

> annah types
> type Even
> data SuccE (predE : Odd)
> data ZeroE
> fold foldEven
> 
> type Odd
> data SuccO (predO : Even)
> fold foldOdd
> <Ctrl-D>

    ... and now these files can be used to build @./Even@ or @./Odd@ values:

> $ morte
> ./Even/SuccE (./Odd/SuccO ./Even/ZeroE )
> <Ctrl-D>
> ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even
> 
> λ(Even : *) → λ(Odd : *) → λ(SuccE : ∀(predE : Odd) → Even) → λ(ZeroE : Even) → λ(SuccO : ∀(predO : Even) → Odd) → SuccE (SuccO ZeroE)

    We can also consume mutually recursive types just by folding them.  Each
    type is already a preformed fold and we can consult each type's respective
    @fold@ function to see what arguments the @fold@ expects:

> $ morte
> ./Even/foldEven
> <Ctrl-D>
> ∀(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even) → ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even
> 
> λ(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Even) → x

> $ morte
> ./Odd/foldOdd
> ∀(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Odd) → ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Odd
> 
> λ(x : ∀(Even : *) → ∀(Odd : *) → ∀(SuccE : ∀(predE : Odd) → Even) → ∀(ZeroE : Even) → ∀(SuccO : ∀(predO : Even) → Odd) → Odd) → x

    If we clean up the type of the @.\/Even\/foldEven@ function we get this:

>     ∀(x : ./Even )
> →   ∀(Even : *)
> →   ∀(Odd : *)
> →   ∀(SuccE : ∀(predE : Odd) → Even)
> →   ∀(ZeroE : Even)
> →   ∀(SuccO : ∀(predO : Even) → Odd)
> →   Even

    Conceptually, when we fold an @./Even@ value using @.\/Even\/foldEven@ we
    just replace each @.\/Even\/SuccE@ constructor with the argument of the fold
    labeled @SuccE@ (i.e. the fourth argument).  Similarly, we substitute each
    @.\/Even\/ZeroE@ constructor with the fifth argument named @ZeroE@ and
    substitute each @.\/Odd\/SuccO@ constructor with the sixth argument named
    @SuccO@.

    We also supply two type parameters named @Even@ and @Odd@.  These type
    parameters must match the input and output of whatever we use to replace
    the @SuccE@, @ZeroE@ and @SuccO@ constructors.

    For example, suppose that we wanted to write a function that converts an
    @./Even@ value to a @./Nat@.  We would just replace every @.\/Even\/SuccE@
    and @.\/Odd\/SuccO@ constructor with @Succ@ and replace every
    @.\/Even\/ZeroE@ constructor with @Zero@, like this:

> $ cat evenToNat.annah
> let evenToNat (e : ./Even ) : ./Nat =
>     ./Even/foldEven e ./Nat ./Nat
>         ./Nat/Succ  -- Replace every `./Even/SuccE` with `Succ`
>         ./Nat/Zero  -- Replace every `./Even/ZeroE` with `Zero`
>         ./Nat/Succ  -- Replace every `./Odd/SuccO`  with `Succ`
> in  evenToNat

    Now we can \"compile\" our @evenToNat@ function to Morte code:

> annah evenToNat.annah > evenToNat

    ... and test that it correctly converts @./Even@ values to their
    equivalent @./Nat@ values:

> $ morte
> ./evenToNat (./Even/SuccE (./Odd/SuccO ./Even/ZeroE ))
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ Zero)

    It works!  We can began with the number two, encoded as an @./Even@ number
    and ended with two encoded as a @./Nat@.

    As before, the @./evenTonat@ function was just performing the desired
    substitution, replacing each @.\/Even\/SuccE@ and @.\/Odd\/SuccO@ with
    @.\/Nat\/Succ@ and replacing @.\/Odd\/ZeroE@ with @.\/Nat\/Zero@:

> ./evenToNat (./Even/SuccE (./Odd/SuccO ./Even/ZeroE ))
>
> -- Constructor substitution
> = ./Nat/Succ (./Nat/Succ ./Nat/Zero )

    Again, this is not the path the compiler takes under the hood, but it's
    equivalent.
-}

{- $prelude
    Annah also comes with a Prelude of utility types and terms.  This Prelude is
    hosted remotely here:

    <http://sigil.place/prelude/annah/1.0/>

    You can visit the above link to browse the Prelude and see what is
    available.

    There are several ways that you can use the Prelude.  The most direct
    approach is to use expressions from the Prelude directly by referencing
    their URLs, like this:

> $ morte
> http://sigil.place/prelude/annah/1.0/Nat/Succ
> (   http://sigil.place/prelude/annah/1.0/Nat/Succ
>     (   http://sigil.place/prelude/annah/1.0/Nat/Succ
>         http://sigil.place/prelude/annah/1.0/Nat/Zero
>     )
> )
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    ... or you can selectively \"alias\" remote references locally by creating
    local files that refer to the remote URLs:

> $ echo "http://sigil.place/prelude/annah/1.0/Nat/Succ" > Succ
> $ echo "http://sigil.place/prelude/annah/1.0/Nat/Zero" > Zero
> $ morte
> ./Succ (./Succ (./Succ ./Zero ))
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero))

    ... or you can \"import\" the entire Prelude into your current directory
    using @wget@:

> $ wget -np -nH -r --cut-dirs=3 http://sigil.place/prelude/annah/1.0/
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

    * Each type (like @./Bool@ or @./Nat@) is a top-level directory.  You can
      reference that type in your code by its directory
    * Each constructor of that type lives underneath the type's directory.  For
      example, @True@ is located underneath the @./Bool@ directory
    * Functions associated with each type are also located underneath the type's
      directory.  For example, the @length@ function is located underneath the
      @./List@ directory.
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
    would be less readable.

    However, if you read in @List/length@ from standard input, then @morte@
    looks for @../List@ expression relative to your present working directory
    and fails.

    Annah's Prelude has some similarities to Haskell's standard libraries and
    some differences.  The rough correspondences are:

    * @(->)@ corresponds to Haskell's @(->)@ type constructor
    * @Bool@ corresponds to Haskell's `Bool` type
    * @Cmd@ corresponds to the operational monad (i.e.
      "Control.Monad.Operational".`Control.Monad.Operational.Program`)
    * @Defer@ corresponds to
      "Data.Functor.Coyoneda".`Data.Functor.Coyoneda.Coyoneda`
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
    * @IO@ corresponds to a very simple `IO` type constructor that only supports
      two operations:

      > ./IO/get : ./IO ./Nat
      > ./IO/put : ./Nat -> ./IO ./Prod0

    In addition to those types, Annah also encodes several of Haskell's type
    classes as values.  Neither Annah nor Morte supports type classes /per se/.
    Instead, each class is encoded as a type constructor and each instance is
    a term of the corresponding type:

    * @Functor@ corresponds to Haskell's `Functor` class
    * @Monoid@ corresponds to Haskell's `Data.Monoid.Monoid` class
    * @Monad@ corresponds to Haskell's `Monad` class
    * @Category@ corresponds to Haskell's `Control.Category.Category` class

    However, the specification of each type class radically differs from how
    Haskell encodes things.  We'll revisit this in a later section.
-}

{- $nats
    The Prelude provides addition and multiplication for natural numbers:

> $ cat > three
> ./Nat/Succ (./Nat/Succ (./Nat/Succ ./Nat/Zero ))
> <Ctrl-D>

> $ morte
> ./Nat/(+) ./three ./three
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ Zero)))))

> $ morte
> ./Nat/(*) ./three ./three
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))

    Also, Annah provides basic syntactic support for natural number literals:

> $ annah | morte
> ./Nat/(+) 3 3
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ Zero)))))

> $ annah | morte
> ./Nat/(*) 3 3
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))

-}

{- $lists
    The Prelude provides operations on lists, too:

> $ annah | morte
> ./List/replicate ./Bool 3 ./Bool/True
> <Ctrl-D>
> ∀(List : *) → ∀(Cons : ∀(head : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → ∀(tail : List) → List) → ∀(Nil : List) → List
> 
> λ(List : *) → λ(Cons : ∀(head : ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool) → ∀(tail : List) → List) → λ(Nil : List) → Cons (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True) (Cons (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True) (Cons (λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True) Nil))

    Annah also provides support for list literals:

> $ annah > bools
> [nil ./Bool , ./Bool/True , ./Bool/False , ./Bool/True ]
> <Ctrl-D>

> $ cat bools
> λ(List : *) → λ(Cons : ∀(head : ./Bool ) → ∀(tail : List) → List) → λ(Nil : List) → Cons ./Bool/True  (Cons ./Bool/False  (Cons ./Bool/True  Nil))

    The general format for lists is:

> [nil elementType, element0, element1, ..., elementN]

    Here are some examples of operations on lists:

> $ morte
> ./List/null ./Bool ./bools
> <Ctrl-D>
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False

> $ morte
> ./List/length ./Bool (./List/(++) ./Bool ./bools ./bools )
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Nil : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Nil : Nat) → Succ (Succ (Succ (Succ (Succ (Succ Nil)))))

> $ annah | morte
> \(a : *) -> \(xs : ./List a) -> ./List/(++) a xs [nil a]
> <Ctrl-D>
> ∀(a : *) → ∀(xs : ∀(List : *) → ∀(Cons : ∀(head : a) → ∀(tail : List) → List) → ∀(Nil : List) → List) → ∀(List : *) → ∀(Cons : a → List → List) → ∀(Nil : List) → List
> 
> λ(a : *) → λ(xs : ∀(List : *) → ∀(Cons : ∀(head : a) → ∀(tail : List) → List) → ∀(Nil : List) → List) → xs

    The last example shows how @morte@ can optimized away @xs ++ []@ to just
    @xs@.
-}

{- $monoids
    Annah also provides several folds on lists, like @sum@ or @and@:

> $ annah | morte
> <Ctrl-D>
> ./Nat/sum [nil ./Nat , 1, 2, 3, 4]
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))))

> $ annah | morte
> <Ctrl-D>
> ./Bool/and [nil ./Bool , ./Bool/True , ./Bool/False , ./Bool/True ]
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False

    What's interesting about these folds is their type:

> $ cat Nat/sum.annah
> let sum : ../Monoid ../Nat = \(xs : ../List ../Nat ) -> xs ../Nat ./(+) 0
> in  sum

> $ cat Bool/and.annah
> let and : ../Monoid ../Bool =
>     \(xs : ../List ../Bool ) -> xs ../Bool ./(&&) ./True
> in  and

    You might have been expecting their types to be something like this:

> sum : ../List ../Nat  -> ../Nat
> and : ../List ../Bool -> ../Bool

    ... and you would have been right because that is actually what their types
    are!  This is because of how @./Monoid.annah@ is defined:

> $ cat Monoid.annah
> let Monoid (m : *) : * = ./List m -> m
> in  Monoid

    In other words, a `Monoid` \"instance\" for a type @m@ is just a function
    that folds a @./List@ of @m@s into a single @m@.  The @./sum@ and @./and@
    functions that fold lists also double as @./Monoid@ instances.

    You can recover the traditional Haskell `Monoid` operations like `mempty`
    and `mappend` from the above @./Monoid@ definition:

> $ cat Monoid/mempty.annah
> let mempty (m : *) (monoid : ./Monoid m) : m =
>     monoid [nil m]
> in  mempty

> $ cat Monoid/mappend.annah
> let mappend (m : *) (monoid : ./Monoid m) (l : m) (r : m) : m =  
>     monoid [nil m, l, r]
> in  mappend

    For example:

> $ morte
> ./Monoid/mempty ./Nat ./Nat/sum
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Zero

> $ annah | morte
> ./Monoid/mappend ./Nat ./Nat/sum 4 5
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))

    However, in practice it's easier to just use the folds directly instead of
    using @.\/Monoid\/mempty@ or @.\/Monoid\/mappend@:

> $ annah | morte
> ./Nat/sum [nil ./Nat ]
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Zero

> $ annah | morte
> ./Nat/sum [nil ./Nat , 4, 5]
> <Ctrl-D>
> ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat
> 
> λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))
-}

{- $commands
    Annah also provides syntactic support for chaining commands using @do@
    notation, in a style very similar to Haskell.  The following examples will
    all give very large outputs so I will tidy the output results, although
    there is not a good way to tidy the output in general:

    For example, here is how you write a list comprehension in Annah.

> $ annah | morte  # Output cleaned up by hand
> ./List/Monad ./Nat (do ./List {
>     x : ./Nat <- [nil ./Nat , 1, 2, 3];
>     y : ./Nat <- [nil ./Nat , 4, 5, 6];
>     _ : ./Nat <- ./List/pure ./Nat (./Nat/(+) x y);
> })
> <Ctrl-D>
>     ∀(List : *)
> →   ∀(Cons : ∀(head : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → ∀(tail : List) → List)
> →   ∀(Nil : List)
> →   List
> 
>     λ(List : *)
> →   λ(Cons : ∀(head : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → ∀(tail : List) → List)
> →   λ(Nil : List)
> →   Cons
>     (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ Zero)))))
>     (   Cons
>         (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ Zero))))))
>         (   Cons
>             (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))
>             (   Cons
>                 (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ Zero))))))
>                 (   Cons
>                     (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))
>                     (   Cons
>                         (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))
>                         (   Cons
>                             (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))
>                             (   Cons
>                                 (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))
>                                 (   Cons
>                                     (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))))
>                                     Nil
>                                 )
>                             )
>                         )
>                     )
>                 )
>             )
>         )
>     )

    ... which is equivalent to:

> ./List ./Nat
>
> [nil ./Nat , 5, 6, 7, 6, 7, 8, 7, 8, 9]

    Annah @do@ notation has a few important differences from Haskell's @do@
    notation:

    * Every command's return type must be annotated; even the final command
    * Braces are required and semicolons are required on all lines
    * You must annotate the monad's type constructor right after the @do@
    * You (usually) wrap the @do@ block in the @./Monad@ instance for your
      type constructor followed by the @do@ block's return value

    Here is an example diagram to illustrate the last rule:

> +-- Monad instance for ./List
> |
> |            +-- The return value of block ...
> |            |
> v            v
> ./List/Monad ./Nat (do ./List {
>     x : ./Nat <- [nil ./Nat , 1, 2, 3];
>     y : ./Nat <- [nil ./Nat , 4, 5, 6];
>     _ : ./Nat <- ./List/pure ./Nat (./Nat/(+) x y);
> })      ^
>         |
>         +-- ... which must match this return value

    You actually don't have to wrap the @do@ block in a @./Monad@ instance, but
    you will get a different result.  Let's see what happens if we omit the
    @./Monad@ instance:

> $ annah | morte  # Output cleaned up by hand
> do ./List {
>     x : ./Nat <- [nil ./Nat , 1, 2, 3];
>     y : ./Nat <- [nil ./Nat , 4, 5, 6];
>     _ : ./Nat <- ./List/pure ./Nat (./Nat/(+) x y);
> }
> <Ctrl-D>
>     ∀(Cmd : *)
> →   ∀(Bind : ∀(b : *) → (∀(List : *) → ∀(Cons : ∀(head : b) → ∀(tail : List) → List) → ∀(Nil : List) → List) → (b → Cmd) → Cmd)
> →   ∀(Pure : (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Cmd)
> →   Cmd
>
>     λ(Cmd : *)
> →   λ(Bind : ∀(b : *) → (∀(List : *) → ∀(Cons : ∀(head : b) → ∀(tail : List) → List) → ∀(Nil : List) → List) → (b → Cmd) → Cmd)
> →   λ(Pure : (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Cmd)
> →   Bind
>     (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat)
>     (   λ(List : *)
>     →   λ(Cons : ∀(head : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → ∀(tail : List) → List)
>     →   λ(Nil : List)
>     →   Cons
>         (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → Succ)
>         (   Cons
>             (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ Zero))
>             (   Cons
>                 (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ Zero)))
>                 Nil
>             )
>         )
>     )
>     (   λ(x : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat)
>     →   Bind
>         (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat)
>         (   λ(List : *)
>         →   λ(Cons : ∀(head : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → ∀(tail : List) → List)
>         →   λ(Nil : List)
>         →   Cons
>             (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>             (   Cons
>                 (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ Zero)))))
>                 (   Cons
>                     (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ Zero))))))
>                     Nil
>                 )
>             )
>         )
>         (   λ(y : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat)
>         →   Bind
>             (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat)
>             (   λ(List : *)
>             →   λ(Cons : ∀(head : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → ∀(tail : List) → List)
>             →   Cons
>                 (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → x Nat Succ (y Nat Succ Zero))
>             )
>             Pure
>         )
>     )

    ... which is equivalent to:

> ./Cmd ./List./Nat
>
>     λ(Cmd : *)
> →   λ(Bind : ∀(b : *) → ./List b → (b → Cmd) → Cmd)
> →   λ(Pure : ./Nat → Cmd)
> →   Bind
>     ./Nat
>     [nil ./Nat , 1, 2, 3]
>     (   λ(x : ./Nat )
>     →   Bind
>         ./Nat
>         [nil ./Nat 4, 5, 6]
>         (   λ(y : ./Nat )
>         →   Bind
>             ./Nat
>             [nil ./Nat (./Nat/(+) x y)]
>             Pure
>         )
>     )

    The @do@ notation is desugaring to a data type named @./Cmd@ that inserts
    placeholders for each @<-@ (pronounced: \"bind\").  In the Haskell world
    this datatype is commonly known as the \"operational\" monad.

    So why did we wrap the @do@ block in @.\/List\/Monad@?  Well, let's check
    out the type of the @.\/List\/Monad@ function:

> $ cat ./List/Monad.annah 
> let Monad: ../Monad ../List
>     =   \(a : *)
>     ->  \(m : ../Cmd ../List a)
>     ->  m (../List a) (\(b : *) -> ./(>>=) b a) (./pure a)
> in  Monad

    Hmmm, that's weird.  Wasn't it supposed to be a function?  Actually, it is!
    To see why, let's check out how @./Monad@ is defined:

> let Monad (m : * -> *) : * = forall (a : *) -> ./Cmd m a -> m a
> in  Monad

    A @./Monad m@ is a function that transforms a @./Cmd m a@ into an @m a@ by
    replacing each @Bind@ with the correct \"bind\" operation for that `Monad`
    and replaces each @Pure@ with the correct \"pure\" operation for that
    `Monad`.  Therefore a @./Monad ./List@ is a function that transforms a
    @.\/Cmd .\/List a@ into a @./List a@.

    That's why we wrap the @do@ block in @.\/List\/Monad@ because the @do@
    block starts out with this type:

> do ./List { ... } : ./Cmd ./List ./Nat

    ... and then when we apply the @.\/List\/Monad function we get back a
    bona-fide @./List@:

> ./List/Monad ./Nat (do ./List { ... }) ./List ./Nat

    There are a couple of parallels between Annah's @./Monad@+@./Cmd@ and
    Annah's @./Monoid@+@./List@:

    * Both of them have syntactic support for building a placeholder of some
      sort.  List notation builds a @./List@ and @do@ notation builds a @./Cmd@
    * Both of them have a way to fold the placeholder into a single value.
      @./Monoid@s fold @./List@s and @./Monad@s fold @./Cmd@s.

-}

{- $io

    Annah also supports a very simplistic @./IO@ type as a proof of concept for
    how you would model a foreign function interface.  For example, here is an
    @./IO@ action that reads a @./Nat@ and writes out the same @./Nat@:

> $ annah
> ./IO/Monad ./Prod0 (do ./IO {
>     n : ./Nat   <- ./IO/get  ;
>     _ : ./Prod0 <- ./IO/put n;
> })
> <Ctrl-D>
> ./IO/Monad  ./Prod0  (λ(Cmd : *) → λ(Bind : ∀(b : *) → ./IO  b → (b → Cmd) → Cmd) → λ(Pure : ./Prod0  → Cmd) → Bind ./Nat  ./IO/get  (λ(n : ./Nat ) → Bind ./Prod0  (./IO/put  n) Pure))

    Annah also provides utilities similar to Haskell for chaining commands, such
    as @.\/Monad\/replicateM_.annah@ which lets you repeat a command a fixed
    number of times:

> $ cat Monad/replicateM_.annah
> let replicateM_ (m : * -> *) (n : ../Nat ) (cmd : m ../Prod0 )
>   : ../Cmd m ../Prod0
>   = ./sequence_ m (../List/replicate (m ../Prod0 ) n cmd)
> in  replicateM_

    Notice that @.\/Monad\/replicateM_@ does not take a @./Monad@ instance as
    an argument.  Instead, @.\/Monad\/replicateM_@ returns a @./Cmd@ which
    you can fold with the appropriate @./Monad@ instance:

    For example:

> $ annah | morte  # Output cleaned up by hand
> ./IO/Monad ./Prod0 (./Monad/replicateM_ ./IO 10 (./IO/put 4))
>     ∀(IO : *)
> →   ∀(Get_ : ((∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO) → IO)
> →   ∀(Put_ : (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO → IO)
> →   ∀(Pure_ : (∀(Prod0 : *) → ∀(Make : Prod0) → Prod0) → IO)
> →   IO
> 
>     λ(IO : *)
> →   λ(Get_ : ((∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO) → IO)
> →   λ(Put_ : (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO → IO)
> →   λ(Pure_ : (∀(Prod0 : *) → ∀(Make : Prod0) → Prod0) → IO)
> →   Put_
>     (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>     (   Put_
>         (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>         (   Put_
>             (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>             (   Put_
>                 (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>                 (   Put_
>                     (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>                     (   Put_
>                         (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>                         (   Put_
>                             (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>                             (   Put_
>                                 (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>                                 (   Put_
>                                     (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>                                     (   Put_
>                                         (λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ Zero))))
>                                         (Pure_ (λ(Prod0 : *) → λ(Make : Prod0) → Make))
>                                     )
>                                 )
>                             )
>                         )
>                     )
>                 )
>             )
>         )
>     )

    If you clean that up a bit you get a syntax tree for printing @4@ 10 times:

>     λ(IO : *)
> →   λ(Get_ : (./Nat → IO) → IO)
> →   λ(Put_ : ./Nat → IO → IO)
> →   λ(Pure_ : ./Prod0 → IO)
> →   Put_ 4 (Put_ 4 (Put_ 4 (Put_ 4 (Put_ 4 (Put_ 4 (Put_ 4 (Put_ 4 (Put_ 4 (Put_ 4 (Pure_ ./Prod0/Make ))))))))))

    Let's try a more complicated program, that reads and writes integers 10
    times:

> $ annah | morte
> let io : ./IO ./Prod0 = ./IO/Monad ./Prod0 (do ./IO {
>     n : ./Nat   <- ./IO/get  ;
>     _ : ./Prod0 <- ./IO/put n;
> })
> in  ./IO/Monad ./Prod0 (./Monad/replicateM_ ./IO 10 io)
> <Ctrl-D>
> ∀(IO : *) → ∀(Get_ : ((∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO) → IO) → ∀(Put_ : (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO → IO) → ∀(Pure_ : (∀(Prod0 : *) → ∀(Make : Prod0) → Prod0) → IO) → IO
> 
> λ(IO : *) → λ(Get_ : ((∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO) → IO) → λ(Put_ : (∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → IO → IO) → λ(Pure_ : (∀(Prod0 : *) → ∀(Make : Prod0) → Prod0) → IO) → Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Get_ (λ(r : ∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat) → Put_ r (Pure_ (λ(Prod0 : *) → λ(Make : Prod0) → Make)))))))))))))))))))))

    ... which if we simplify we get:

>     λ(IO : *)
> →   λ(Get_ : (./Nat → IO) → IO)
> →   λ(Put_ : ./Nat → IO → IO)
> →   λ(Pure_ : ./Prod0 → IO)
> →   Get_ (λ(r : ./Nat ) →
>       Put_ r (
>         Get_ (λ(r : ./Nat ) →
>           Put_ r (
>             Get_ (λ(r : ./Nat ) →
>               Put_ r (
>                 Get_ (λ(r : ./Nat ) →
>                   Put_ r (
>                     Get_ (λ(r : ./Nat ) →
>                       Put_ r (
>                         Get_ (λ(r : ./Nat ) →
>                           Put_ r (
>                             Get_ (λ(r : ./Nat ) →
>                               Put_ r (
>                                 Get_ (λ(r : ./Nat ) →
>                                   Put_ r (
>                                     Get_ (λ(r : ./Nat ) →
>                                       Put_ r (
>                                         Get_ (λ(r : ./Nat ) →
>                                           Put_ r (
>                                             Pure_ ./Prod0/Make))))))))))))))))))))

    In other words, we've built an abstract syntax tree representing ten
    @Get_@ and @Put_@ nodes where each @Get_@ node threads its result to the
    next @Put_@ node.

    Annah cannot run this abstract syntax tree since Annah does not have a
    backend to interpret this tree.  The most Annah can do is model effects
    without running them.
-}

{- $paths
    Annah provides support for the `Category` type class, too, using an approach
    very similar to the support for `Monoid` and `Monad`:

    * Provide a placeholder type named @./Path@ (which is a \"free category\")
    * Provide syntactic support for building @./Path@s
    * Define a @./Category@ to be something that folds @./Path@s

> $ cat Category.annah
> let Category (cat : * -> * -> *) : * =
>     forall (a : *) -> forall (b : *) -> ./Path cat a b -> cat a b
> in  Category

    Here is an example of composing several functions using the @./Category@
    instance for functions:

> $ annah | morte
> let even (n : ./Nat ) : ./Bool = n ./Bool ./Bool/not ./Bool/True
>
> in  let f : ./List ./Nat -> ./Bool =
>     ./(->)/Category (./List ./Nat ) ./Bool
>         [id ./(->) { ./List ./Nat } ./Nat/sum { ./Nat } even { ./Bool } ./Bool/not { ./Bool }]
>
>     in  f [nil ./Nat , 1, 2, 3, 4
> <Ctrl-D>
> ∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool
> 
> λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False

    The above code creates a composition chain of three functions, reading from
    left to right:

    * @.\/Nat/sum@, which has type @.\/List .\/Nat -> .\/Nat@
    * @even@, which has type @.\/Nat -> .\/Bool@
    * @.\/Bool\/not@, which has type @.\/Bool -> .\/Bool@

    Annah's path notation requires you to annotate the types along the way as
    you compose each component.  In the above example, you can find each
    function's input type immediately to the left of that function and the
    output type immediately to the right of each function.  Types are surrounded
    by braces to separate them from the things you compose.

    Annah's path notation differs from lists in a couple of ways:

    * You replace @nil@ with @id@
    * The @id@ is followed by the type constructor that you are chaining
    * You replace commas with intermediate types

    You may find the notation easier to read if you put each composable
    component on a separate line preceded by the corresponding input type:

> let even (n : ./Nat ) : ./Bool = n ./Bool ./Bool/not ./Bool/True
>
> in  let f : ./List ./Nat -> ./Bool =
>     ./(->)/Category (./List ./Nat ) ./Bool [id ./(->)
>         { ./List ./Nat } ./Nat/sum
>         { ./Nat        } even
>         { ./Bool       } ./Bool/not
>         { ./Bool       }
>     ]
>
>     in  f [nil ./Nat , 1, 2, 3, 4]

    Annah's Prelude only provides support for one @./Category@ instance for
    functions named @./(->)/Category@, so in practice the @./Category@ support
    is not that handy out-of-the box and is mainly provided for completeness.
-}

{- $conclusion
    Those are all the features that Annah supports!  Annah is a very tiny
    language and library that illustrates and implements basic idioms for
    translating functional programming concepts into pure lambda calculus.

    Hopefully you can use Annah to learn how to encode a subset of Haskell in a
    completely total programming language.  If you translate any Haskell
    functions to Annah you can contribute them upstream to the Annah prelude by
    submitting a pull request against the Annah repository:

    <https://github.com/Gabriel439/Haskell-Annah-Library/tree/master/Prelude>
-}
