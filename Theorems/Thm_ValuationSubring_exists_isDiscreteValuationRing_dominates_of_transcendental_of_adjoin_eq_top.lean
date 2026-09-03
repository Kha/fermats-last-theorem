import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_transcendental_of_adjoin_eq_top

set_option autoImplicit false

universe u v

open IsLocalRing

theorem ValuationSubring.exists_isDiscreteValuationRing_dominates_of_transcendental_of_adjoin_eq_top
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    (x : E) (hx : Transcendental F x) (hE : IntermediateField.adjoin F ({x} : Set E) = ⊤)
    (W : ValuationSubring F) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring E, IsDiscreteValuationRing ↥V ∧
      (∀ y : F, y ∈ W → algebraMap F E y ∈ V) ∧
      (∀ y : ↥W, y ∈ maximalIdeal ↥W → algebraMap F E (y : F) ∈ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_transcendental_of_adjoin_eq_top.solution
