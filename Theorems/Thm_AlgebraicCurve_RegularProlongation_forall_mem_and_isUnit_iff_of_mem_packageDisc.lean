import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_forall_mem_and_isUnit_iff_of_mem_packageDisc
attribute [-instance] AlgebraicCurve.SemistableModel.Descent.commRing AlgebraicCurve.SemistableModel.Descent.isNoetherianRing AlgebraicCurve.SemistableModel.Descent.isProper₀ AlgebraicCurve.SemistableModel.Descent.isIntegral₀ AlgebraicCurve.SemistableModel.isProper AlgebraicCurve.SemistableModel.flat AlgebraicCurve.SemistableModel.Descent.henselianLocalRing AlgebraicCurve.SemistableModel.locallyOfFinitePresentation AlgebraicCurve.SemistableModel.Descent.isLocalHom AlgebraicCurve.SemistableModel.Descent.isAlgebraic AlgebraicCurve.SemistableModel.Descent.isAlgebraic_F₀ AlgebraicCurve.SemistableModel.Descent.locallyOfFinitePresentation₀ AlgebraicCurve.SemistableModel.isIntegral AlgebraicCurve.SemistableModel.Descent.flat₀ AlgebraicCurve.SemistableModel.isClosedImmersion_specMap_residue
attribute [-simp] AlgebraicCurve.SemistableModel.mk.injEq AlgebraicCurve.SemistableModel.mk.sizeOf_spec AlgebraicCurve.SemistableModel.Descent.mk.injEq AlgebraicCurve.SemistableModel.Descent.mk.sizeOf_spec

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.forall_mem_and_isUnit_iff_of_mem_packageDisc
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (S : Subring F) (φT : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A) (Dp : Set (Place L F))
    (hpk :
            (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
            (φT).FormallySmooth ∧ (φT).FormallyUnramified ∧
            (∀ a : ↥A, ((φT (Polynomial.C a) : ↥(S)) : F) = algebraMap L F (a : L)) ∧
            (∀ a : ↥A, χ₀ (φT (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φT Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φT Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φT Polynomial.X : ↥(S)) : F) ∈ R.integers,
              Q.ord (R.residue ⟨((φT Polynomial.X : ↥(S)) : F), hR⟩) = 1) ∧
            (∀ P, P ∈ Dp ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ Dp ∧ ∀ f : ↥(S), P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
            (∀ P ∈ Dp, ∀ f : F, f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
            (∀ f : F, f ≠ 0 → (∀ P ∈ Dp, P.ord f = 0) →
              ∃ (c : L) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥(S)) : F)) ∧
            (∀ f : F, f ∈ R.integers → (∀ P ∈ Dp, f ∈ P.toValuationSubring) → f ∈ S))
    (P : Place L F) (hP : P ∈ Dp) :
    ∀ f : F, f ∈ S → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
      (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ S, f * g = 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_forall_mem_and_isUnit_iff_of_mem_packageDisc.solution
