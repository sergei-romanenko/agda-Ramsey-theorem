# Intuitionistic Ramsey Theorem

A formalisation of "A direct proof of Ramsey’s Theorem",
a note by Thierry coquand, version of October 24, 2011,
formalised by David Wahlstedt (david.wahlstedt@gmail.com),
November 2011, work funded by the Swedish Research Council,
project reg no: 2008:6902.

The content of the directory `original` has been taken from

* <http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.IntuitionisticRamseyTheorem>

The directory `revised` contains a revised version, produced by
some refactoring of the source version.

The purpose of this refactoring is twofold:

* To reuse the stuff provided by the Standard Library.
This can be useful in cases where the proof has to be
embedded into another Agda project based on the Standard library.

* To make the form of the proof more "human-friendly".
In particular, by the extensive use of `Relation.Binary.PreorderReasoning`.

(It goes without saying that the notion of "human-friendly"
is rather subjective one. Hence it is the original version that
may be considered by some readers as more natural and easier to read. :-) )

This version is compatible with

* Agda 2.4.0.2
* The Standard Library 0.8

