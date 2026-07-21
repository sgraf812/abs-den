import Iris.Algebra.COFESolver

/-! Fast-runtime companion to iris-lean's COFE-solver isomorphism.

`OFunctor.Fix.iso` is opaque with the tower-based runtime; code that runs it
(`Trace.map`/`bind`, `D.fold`/`unfold`) still pays per-level conversions on
recirculated values. In the limit the tower's coherence maps are identities,
so `fold`/`unfold` are the identity coercion. `Fix.unsafeIso` expresses that,
baked into `Fix.fastIso` at its (local) def site, since `implemented_by`
cannot decorate the imported `Fix.iso`. Downstream uses the `fast` variants;
they are definitionally the original, so the solver's `≡` laws apply. -/

open Iris Iris.COFE OFE

namespace Iris.COFE.OFunctor

universe u
variable {F : ∀ α β [COFE α] [COFE β], Type u} [OFunctorContractive F]
variable [∀ α [COFE α], IsCOFE (F α α)]
variable [Inhabited (F (ULift Unit) (ULift Unit))]

open Fix.Impl in
unsafe def Fix.unsafeIso : OFE.Iso (F (Fix F) (Fix F)) (Fix F) where
  hom := ⟨fun x => unsafeCast (show Tower F from ⟨fun _ => unsafeCast x, lcProof⟩), lcProof⟩
  inv := ⟨fun X => unsafeCast (Tower.val (show Tower F from unsafeCast X) 0), lcProof⟩
  hom_inv := lcProof
  inv_hom := lcProof

@[implemented_by Fix.unsafeIso]
opaque Fix.fastIso : OFE.Iso (F (Fix F) (Fix F)) (Fix F) := Fix.iso

def Fix.fastFold : F (Fix F) (Fix F) -n> Fix F := Fix.fastIso.hom
def Fix.fastUnfold : Fix F -n> F (Fix F) (Fix F) := Fix.fastIso.inv
theorem Fix.fastFold_fastUnfold (X : Fix F) : Fix.fastFold (Fix.fastUnfold X) ≡ X :=
  Fix.fastIso.hom_inv
theorem Fix.fastUnfold_fastFold (X : F (Fix F) (Fix F)) : Fix.fastUnfold (Fix.fastFold X) ≡ X :=
  Fix.fastIso.inv_hom

attribute [irreducible] Fix.fastFold Fix.fastUnfold

end Iris.COFE.OFunctor
