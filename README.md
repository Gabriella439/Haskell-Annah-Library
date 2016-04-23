# Annah v1.0.0

Annah is a medium-level total language that compiles down to the calculus of
constructions
(specifically [Morte](https://github.com/Gabriel439/Haskell-Morte-Library)).

Annah exists primarily as a reference implementation for encoding higher-level
idioms in pure lambda calculus.  Many of these tricks are scattered among papers
and folklore but have never been consolidated into a single focused
implementation that people could learn from, experiment with, or fork for their
own uses.

Annah is not just a compiler but also a Prelude which translates a small subset
of Haskell to pure and total lambda calculus.  The latest Prelude is hosted
online [here](http://sigil.place/prelude/annah/1.0/) and can be referenced
directly within Annah or Morte expressions.

## Quick start

* Install [the `stack` tool](http://haskellstack.org/)
* `stack setup`
* `stack install annah`

This creates the `annah` executable under `stack`'s default `bin` directory
(typically `~/.local/bin/` on Unix-like systems).  This executable reads Annah
expressions from `stdin`, type-checks them, and outputs the equivalent Morte
expression to `stdout`.  For example:

```bash
$ annah | morte
type Bool
data True
data False
fold if
in

type Nat
data Succ (pred : Nat)
data Zero
fold foldNat
in

let not (b : Bool) : Bool = if b Bool False True
in

let even (n : Nat) : Bool = foldNat n Bool not True
in

even (Succ (Succ (Succ Zero)))
<Ctrl-D>
∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False
```

You can also reference any expression from the Prelude directly by URL.  For
example, we can transform the above example to use the Prelude like this:

```bash
$ annah | morte
let even (n : http://sigil.place/prelude/annah/1.0/Nat )
    : http://sigil.place/prelude/annah/1.0/Bool =
    n   http://sigil.place/prelude/annah/1.0/Bool
        http://sigil.place/prelude/annah/1.0/Bool/not
        http://sigil.place/prelude/annah/1.0/Bool/True
in

even
(   http://sigil.place/prelude/annah/1.0/Nat/Succ
    (   http://sigil.place/prelude/annah/1.0/Nat/Succ
        (   http://sigil.place/prelude/annah/1.0/Nat/Succ
            http://sigil.place/prelude/annah/1.0/Nat/Zero
        )
    )
)
<Ctrl-D>
∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False
```

You can clone the Prelude locally and refer to expression by their local path,
too:

```bash
$ wget -np -nH -r --cut-dirs=3 http://sigil.place/prelude/annah/1.0/
$ annah | morte
let even (n : ./Nat ) : ./Bool = n ./Bool ./Bool/not ./Bool/True

in  even (./Nat/Succ (./Nat/Succ (./Nat/Succ ./Nat/Zero )))
<Ctrl-D>
∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False
```

`annah` also provides syntactic support for certain data types, like numeric
literals, so we can shorten this further to:

```bash
$ annah | morte
let even (n : ./Nat ) : ./Bool = n ./Bool ./Bool/not ./Bool/True

in  even 3
<Ctrl-D>
∀(Bool : *) → ∀(True : Bool) → ∀(False : Bool) → Bool

λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → False
```

Here's a more advanced example of a list comprehension written in Annah:

```bash
$ annah | morte
let xs : ./List ./Nat = ./List/Monad ./Nat (do ./List {
        x : ./Nat <- [nil ./Nat , 1, 2, 3];
        y : ./Nat <- [nil ./Nat , 4, 5, 6];
        _ : ./Nat <- ./List/pure ./Nat (./Nat/(+) x y);
    })
in  ./Nat/sum xs
<Ctrl-D>
∀(Nat : *) → ∀(Succ : ∀(pred : Nat) → Nat) → ∀(Zero : Nat) → Nat

λ(Nat : *) → λ(Succ : ∀(pred : Nat) → Nat) → λ(Zero : Nat) → Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
```

To learn more about Annah, read the
[Annah tutorial](http://hackage.haskell.org/package/annah/docs/Annah-Tutorial.html).

## How to contribute

Annah is mostly a reference implementation of some things that I've learned
along the way towards building a real production language.  That means that I'm
less likely to improve the polish, error messages, or type inference of Annah,
since I'm dedicating those efforts to a real programming language that will
resemble Annah but provide support for high-efficiency text and numeric
primitives and a real `IO` backend.  However, I will still listen to all feature
requests and if you strongly feel that Annah should be improved in some way
then feel free to open an issue.

Just keep in mind that Annah's primary focus is providing a small, clean, and
easy to understand implementation that other people can easily learn from and
fork to modify to their needs.  That means that I will push back on anything
that greatly complicates the implementation.  Vice versa, anything that
simplifies the implementation is very welcome!

I also welcome contributions to Annah's prelude which you can find here:

https://github.com/Gabriel439/Haskell-Annah-Library/tree/master/Prelude

... and I will periodically upload versioned Preludes online here:

http://sigil.place/prelude/annah/

... so that people can import expressions directly within their own code by
URL.

## Development Status

[![Build Status](https://travis-ci.org/Gabriel439/Haskell-Annah-Library.png)](https://travis-ci.org/Gabriel439/Haskell-Annah-Library)

Annah is heavily exercised by the Annah Prelude so most bugs should have been
rooted out by this point.  The most likely bugs that still remain at this point
are bugs in the desugaring logic not correctly avoiding name capture.

The most likely thing to change in the API is support for new desugaring rules
if people request them and are willing to implement them.

## License (BSD 3-clause)

Copyright (c) 2016 Gabriel Gonzalez
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice, this
  list of conditions and the following disclaimer in the documentation and/or
  other materials provided with the distribution.

* Neither the name of Gabriel Gonzalez nor the names of other contributors may
  be used to endorse or promote products derived from this software without
  specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
