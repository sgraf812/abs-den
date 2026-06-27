# Lean formalization conventions

The library is in `AbsDen/World/Basic.lean`. Key combinators:
`▷` (`Later.prop`), `Later.next`, `Later.next'`, `Later.ap'`, `Later.ap`,
`Later.hmap`, `Later.map`, `Later.elim`, `Later.sequence`, `loeb`,
`World.Pred`, `World.Pred.ofClosed`, `World.Function`, `World.Function.Natural`,
`World.Const`, `World.Comp`, `World.Prod`, `World.Sum`, `World.IProp`,
`World.restrictStep`, `World.restrict`. Use them.

## Combinators first, definitions last

Before any new `def`, write the body in terms of existing combinators. If you
can't, you're missing a combinator — find it in `World/Basic.lean` or extract a
new reusable one in there. Don't inline by pattern-matching on `Nat` at the use
site.

If you've added 3+ helpers in a session without citing existing combinators,
stop and audit — most likely you're duplicating infrastructure.

## Never pattern-match on level

`def f | 0 => True | _+1 => …` is wrong. The `0 ⟹ True` collapse is precisely
what `▷` exists for. Use `Later.prop` (`▷`), `Later.elim`, `Later.ap'`,
`Later.next`, `Later.hmap`. If you reach for `match l with | 0 | l'+1`, you're
working externally to the topos instead of internally.

## Guarded recursion goes through `loeb`

Predicate-level recursion: `loeb : World.Function (Later A) A n → A n`. The
body takes the guarded recursive ref via `Later`, returns the predicate.
Don't write `def f | n+1 d => … f n …` directly — `loeb` is precisely the
combinator for this, with the right naturality already proven via
`loeb.eq` and `World.Function.Natural`.

## `∀ m ≤ n, …m…` is a smell

Externalized Kripke quantification means you're translating instead of
working internally. Look for the `World.Pred D` or `world(…)` form first.
The closure laws of `World.Pred` carry the all-sub-levels information; let
them. The `world(…)` notation is for World.Function arrow types
(`world(A → B) n = ∀ m ≤ n, A m → B m` packaged); reach for it before
writing the `∀` by hand.

## Scrap before patch

When a definition or proof shape is wrong, delete and restart. The "make
Lean accept this" instinct produces worse code than the "find the right
abstraction" instinct. A working proof of the wrong shape is worse than no
proof — it ossifies the bad shape and breeds bridge lemmas to compensate.
