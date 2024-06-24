SG:
* Overhaul Related Work
* Decide about Boxity Analysis
* Write DmdAnal Appendix
* Update Annotations Appendix
* Update Soundness Appendix with new formulation of Galois Connection
* Update Agda Appendix (perhaps some things changed since I last touched it?)
* Think about modular BetaApp

* [x] Clarify what is formalised in Agda

Rev A
-----

- [-] The definition of figure 1 is not explained.

- [x] Line 146: this footnote, at this place in the text begs the question
  of whether this fixpoint is well defined (does it exist? in which
  partially-ordered set?)

- [-] Lines 155-166: the example is explained step by step, but this is
  hardly informative. It provides no explanation or no intuition of
  why this computation makes sense for absence analysis.

- [-] Line 175: the pre-order relation ⊑ should probably be introduced and
  explained earlier

- [-] Lines 263-271: this is obscure. The text depends too heavily on the
  contents of the appendix.

- [x] Figure 2, rule Let1: at this point, we notice that let bindings are
  recursive, it seems, as opposed to the let bindings of the language
  of section 2.1. A surprise for the reader.

- [x] Figure 2, rule Look(y): recording the variable `y` is a difference
  with the LK or the MarkII machines. The cases where x <> y are
  interesting for the reader, and the last example of section 3
  illustrate such a case. It is however not explained, and the reader
  has to understand/discover this point alone.

- [x] Figure 5: you have chosen that `fun` takes a variable as a first
  parameter (the bound variable of the function). Why didn't you make
  similar choices for constructs that also involve bound variables?
  (bind, select)

- [-] Figure 6 is useless, since the reader has to complete the definition
  by herself!

- [-] The statement of Theorem 4 (Strong Adequacy) and its proof are too
  sketchy. I am not sure what the theorem statement really means.

- [x] Line 908: "Occurrences of x must make do with the top value".
  I don't understand the sentence.

- [x] Lines 923-926: "Much more could be said about..." Either say it, or
  do not mention it at all. I have no idea what you have in mind.

- [x] Line 930 (footnote 24): please explain what you mean.

- [?] Figure 12: it is very upsetting that `lub` is not used at all in
  this definition...

- [x] Line 958: "The keen reader may feel indignant..." It is generally a
  good idea to avoid the reader entering a state of anger. Please
  rephrase the explanation so that it does not happen.

- [x] Lines 960-961: "This is easily worked around in practice by
  employing appropriate widening measures such as bounding the depth
  of ValueU". Could you please give the definition, then, if you
  actually had to implement such measures? Does it have consequences
  about monotonicity?

- [x] Lines 978-979 (footnote 25): "Never mind totality; why is the use of
  least fixpoints even correct?". Is this an remark that was targeted
  to the authors discussing a point while writing the paper, or is is
  targeted to the reader? Should the reader give you the answer?
  Please rephrase.

- [x] Figure 13: please explain rules Unwind-Stuck and Intro-Stuck. The
  use of join in those rules seems rather surprising.

- [x] Lines 1004-1007: this is obscure.

- [x] Lines 1012-1015: this is not a proof rule. Please state what you
  mean precisely.

- [x] Line 1018: "opinionated". Please use a more scientific vocabulary.
  This is not a blog post.

- [x] Lines 1022-1023: "considering the final heap for nested abstraction
  (the subtle details are best left to the Appendix)". I don't have
  the slightest idea of what you mean...

- [-] Lines 1142-1147: "... but it does not make any claim on whether a
  transformation conditional on some trace property is actually sound,
  yet alone an improvement, etc". Again, this is obscure. Please
  explain. I don't understand why your interpreter would not be
  appropriate for dead code elimination either.

- [x] Lines 1169-1170: "we think that CFA can be used to turn any finite
  Trace instance such as TU into a static analysis without the need to
  define a custom summary mechanism". I don't understand what you have
  in mind.

- [x] Lines 1197-1201: What do you mean? That you are not able to model
  demand transformers?

Rev B
-----

- [x] What is the source language? It took me a while to figure out that
  let-bindings are recursive (this may be obvious for readers with a
  Haskell background, but less obvious for those with a Standard ML or
  Agda background).  Likewise, it took me a while to realise that the
  source language is untyped.  Tell me!

- [ ] What exactly do you achieve? In particular, what's the relation
  between the Agda artefacts and the Haskell artefacts — the Agda code
  is subtly (?) different to guarantee well-definedness.  Which
  theorems enjoy ``only'' pencil-and-paper proofs — what's the
  setting?  set theory? domain theory (CPOs)?, which theorems are
  fully mechanised?

- [x] There are too many footnotes for my taste.

- [ ] Add more on static analysis

Rev C
-----

- [x] (Remove CCbV?)
