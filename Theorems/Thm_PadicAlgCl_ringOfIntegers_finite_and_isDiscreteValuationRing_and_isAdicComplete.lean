import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete

set_option autoImplicit false

theorem PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    Module.Finite ℤ_[p] (PadicAlgCl.ringOfIntegers p K) ∧
    ∃ _ : IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p K),
      IsAdicComplete (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K))
        (PadicAlgCl.ringOfIntegers p K) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete.solution
