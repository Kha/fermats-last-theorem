import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_forall_localSubring_iff_forall_localization

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Place.forall_localSubring_iff_forall_localization
    {L F : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (N₀ : Subring F) [IsLocalRing ↥N₀] (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (𝔭 : Ideal ↥T)
    (h𝔭 : 𝔭 = Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}))
    (Lx : Subring F) (hLx : ∀ f : F, f ∈ Lx ↔ ∃ b c : ↥T, c ∉ 𝔭 ∧ f * (c : F) = (b : F))
    (P : Place L F) (hP : P.IsRational) :
    ((∀ f : F, f ∈ N₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥N₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨P.evalAt (f : F), h⟩ : ↥A) ∈ maximalIdeal ↥A)) ↔
    (∀ f : F, f ∈ Lx → f ∈ P.toValuationSubring ∧
        ∃ h : P.evalAt f ∈ A, (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ Lx, f * g = 1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_forall_localSubring_iff_forall_localization.solution
