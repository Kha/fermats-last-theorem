import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_place_evalAt_eq_of_section_of_ker_eq_span

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_place_evalAt_eq_of_section_of_ker_eq_span
    {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (S : Subring F) [IsLocalRing ↥S]
    (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
    (hfrac : ∀ f : F, ∃ a b : ↥S, (b : F) ≠ 0 ∧ f * (b : F) = (a : F))
    (T : ↥S) (c : ↥A) (hTc : (T : F) ≠ algebraMap L F (c : L))
    (χ : ↥S →+* ↥A) (hχa : ∀ a : ↥A, χ ⟨algebraMap L F (a : L), hAS a⟩ = a) (hχT : χ T = c)
    (hker : RingHom.ker χ = Ideal.span {T - ⟨algebraMap L F (c : L), hAS c⟩})
    (hnoeth : ∀ O : Subring F, (∀ f : F, f ∈ O ↔ ∃ a b : ↥S, b ∉ RingHom.ker χ ∧ f * (b : F) = (a : F)) →
      IsNoetherianRing ↥O) :
    ∃ P : Place L F,
      (∀ f : F, f ∈ P.toValuationSubring ↔ ∃ a b : ↥S, b ∉ RingHom.ker χ ∧ f * (b : F) = (a : F)) ∧
      (∀ g : ↥S, P.evalAt (g : F) = ((χ g : ↥A) : L)) ∧
      (∀ g : F, g ∈ S → g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A,
        (IsUnit (⟨P.evalAt g, h⟩ : ↥A) ↔ ∃ g' ∈ S, g * g' = 1)) ∧
      P.evalAt (T : F) = (c : L) ∧
      (∀ s : F, s ∈ S → P.evalAt s = 0 →
        ∃ s' : F, s' ∈ S ∧ s = ((T : F) - algebraMap L F (c : L)) * s') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_place_evalAt_eq_of_section_of_ker_eq_span.solution
