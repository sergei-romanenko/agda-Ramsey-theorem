module Everything where

--------------------------------------------------------------------------------

-- A formalisation of "A direct proof of Ramsey’s Theorem", a note by
-- Thierry coquand, version of October 24, 2011, formalised by David
-- Wahlstedt (david.wahlstedt@gmail.com), November 2011, work funded
-- by the Swedish Research Council, project reg no: 2008:6902.

-- This is part of joint work, the paper "Stop when you are
-- Almost-Full, Adventures in constructive termination", by Dimitrios
-- Vytiniotis, Thierry Coquand, and David Wahlstedt, submitted for ITP
-- 2012 (http://itp2012.cs.princeton.edu/). There, the result in
-- Coquand's note is used (in a Coq development by Vytiniotis) to give
-- a constructive justification of Size-Change Termination (SCT), (Lee,
-- Jones, Ben-Amram, 2001), among other things.

-- This formalisation uses only very basic type theory.  In some of
-- the main lemmas we use non-trivial termination arguments: by
-- lexicographic recursion, which can be reduced directly to
-- (higher-order) primitive recursion. Note that Size-Change
-- Termination is supported (yet without formal justification) in
-- Agda, but this is *not* needed in this formalisation, which is
-- important, if we want to use it for justifying SCT.

--------------------------------------------------------------------------------

-- The Intuitionistic Ramsey Theorem (IRT) states that the
-- intersection of two almost full relations is almost full. An n-ary
-- relation R over a given set X, is "almost full", in the classical
-- sense, when each infinite sequence over X has a finite prefix
-- containing a sub-sequence on length n satisfying R. This is
-- constructively described as an inductive bar property. It can be
-- shown classically that IRT is equivalent with the infinite version
-- of Ramsey's Theorem.

--------------------------------------------------------------------------------

-- Some basic types and logical facts

import Prelude

-- A distrubutive lattice D with elements a, b, c, and operations ×
-- and ⊎, neutral element ₁. In this formalisation D is instantiated
-- to predicates over finite sequences of a given set X. The following
-- module defines some list predicate transformers and proves
-- properties about them.

import ListPredicate

-- The main result

import IRT


