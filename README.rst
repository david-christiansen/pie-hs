==============
Pie in Haskell
==============

This is a port of Pie from Racket to Haskell.

This is intended to be as clear and simple as possible. Clarity and
simplicity are more important than performance, but less important
than correctness. To help achieve this, the code adheres to the
following dogmas:

 1. As few dependencies as possible - currently just base, text, and text-icu.
 2. Absolutely no language extensions. Haskell 2010 only.
 3. No monad transformers
