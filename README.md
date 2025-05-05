# mmverify.py and MeTTaMath

## MeTTaMath
MeTTaMath is a project to import the Metamath library into MeTTa.
[MeTTa](https://metta-lang.dev/) is a programming language designed to be the development and cognitive language for AGI systems. The core of MeTTa is pattern matching and rewriting. This aligns naturally with Metamath's core inference rule of variable substitution, making integration conceptually elegant.


## Current Status
The verify() function has been implemented in MeTTa. The project currently processes Metamath .mm files during Python parsing, adding relevant information to MeTTa spaces. Full MeTTa parsing and remaining verification checks are still in development. Performance is currently about 5000x slower than the Python version, but future integration with MORK should offer interesting optimization opportunities.


## Repository Structure

* mmverify-utils.metta - Contains the main implementation of the verify() and treat_step() functions, along with utility functions
* mmverify.py - The original Python Metamath verifier by Raph Levien, modified with MeTTa integration code
* examples/ - Contains examples of MeTTa interpretation of Metamath statements and their output

---

This is a Metamath verifier written in Python, originally by Raph Levien.

Metamath is a formal language and an associated computer program (a proof checker) for archiving, verifying, and studying mathematical proofs.  The set of proved theorems using Metamath is [one of the largest bodies of formalized mathematics](http://us.metamath.org/mm_100.html). Multiple Metamath verifiers (written in different languages by different people) are used to verify them, reducing the risk that a software defect will lead to an incorrectly verified proof.

For a quick introduction to Metamath and its goals, see the video
[Metamath Proof Explorer: A Modern Principia Mathematica](https://www.youtube.com/watch?v=8WH4Rd4UKGE).

For more information about Metamath, see the [Metamath website](http://us.metamath.org/).

You can also get the (physical) book about Metamath; see: [*Metamath: A Computer Language for Mathematical Proofs* by Norman Megill & David A. Wheeler, 2019, ISBN 9780359702237](http://www.lulu.com/shop/norman-megill-and-david-a-wheeler/metamath-a-computer-language-for-mathematical-proofs/hardcover/product-24129769.html).

This software is free-libre / open source software (FLOSS) released under the MIT license.
