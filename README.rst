==============
Pie in Haskell
==============

This is an implementation of Pie, the language from *The Little Typer*, in Haskell.



How to Use It
-------------

Compile the program with ``cabal v2-build``. Run the tests with
``cabal v2-test``. Once it works, use ``cabal v2-install`` to install
the binary somewhere.

This implementation of Pie can be run in two modes:

- An interactive REPL

- A batch-mode processor

To start the REPL, invoke ``pie`` without a filename as an
argument. To process a Pie file in batch mode, use ``pie FILENAME``.

To learn Pie, please consult *The Little Typer*. If you need to refresh
your memory, please consult the `language reference`_.

.. _`language reference`: https://docs.racket-lang.org/pie/

REPL Commands
-------------
An expression
  Expressions are treated as examples to be type checked and evaluated.

A declaration
  Declarations, such as claims, definitions, and ``check-same`` forms,
  are treated as if they were in a file. Claims and definitions are
  added to the context, and ``check-same`` checks sameness
  immediately.

``:verbose``
  Switch Pie to verbose mode.

``:concise``
  Switch Pie to concise mode.

``:load FILE``
  Load ``FILE``, throwing away the current context.

Concise and Verbose Modes
-------------------------

In concise mode, Pie emits only the information about the user's
program that is explicitly requested. In other words, it will display
error messages and the explicit results of examples that the user has
requested.

In verbose mode, Pie additionally displays information about the type
of each subexpression that it successfully checks. While this
information could serve as the basis for a good editor plugin, this
has not yet been implemented.

Readline support
----------------

The REPL in this implementation of Pie does not support arrow keys or
other similar features. You can get rudimentary support for them using
``rlwrap``.

Design Guidelines
-----------------

This implementation of Pie is intended to be as clear and simple as
possible. Clarity and simplicity are more important than performance,
but less important than correctness. To help achieve this, the code
adheres to the following dogmas:

1. As few dependencies as possible - currently just base, text, and
   text-icu. More dependencies are allowed in the test suite.

2. Absolutely no language extensions. Haskell 2010 only.

3. No monad transformers.
