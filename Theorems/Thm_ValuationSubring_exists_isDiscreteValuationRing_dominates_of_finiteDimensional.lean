import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional

set_option autoImplicit false

universe u v

open IsLocalRing

theorem ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (W : ValuationSubring F) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring E, IsDiscreteValuationRing ↥V ∧
      (∀ x : F, x ∈ W → algebraMap F E x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap F E (x : F) ∈ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.solution
