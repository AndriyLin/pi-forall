Pi-Forall language
------------------

One thing I found it different, is that they care not only about defining the relation, but also about translating them into algorithms. What I've learned so far, instead, focus more on just defining the relation prove them, I didn't care that much about their actual implementation.

---

This language implemention is designed to accompany four lectures at
OPLSS during Summer 2014. Notes for these lectures are available at:

- [notes.md](notes.md):    Basic language with Type:Type 
- [notes2.md](notes2.md):  Implementation of basic languages
- [notes3.md](notes3.md):  Definitional and propositional equality
- [notes4.md](notes4.md):  Datatypes, with parameters and indices, erased arguments

Each set of lecture notes corresponds to an increasingly expressive demo
implementation of dependently-typed lambda calculus.

- [version1/](version1/):   Basic language implementation, 
- [version2/](version2/):   Language extended with nontrivil definitional equality
- [soln/](soln/):           Language with datatypes and erased arguments

All of these versions are excerpted from the marked up files in the directory:

- [master/](master/)

All edits should be to the code in the `master` directory. The above versions
are included in the repo just for convenience.

--
Stephanie Weirich, June 2014
