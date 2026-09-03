import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top

set_option autoImplicit false

universe u v

open IsLocalRing

theorem ValuationSubring.exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (s : Finset L) (hs : IntermediateField.adjoin K (s : Set L) = ⊤)
    (W : ValuationSubring K) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ x : K, x ∈ W → algebraMap K L x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap K L (x : K) ∈ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top.solution
