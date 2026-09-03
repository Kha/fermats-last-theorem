import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

theorem NumberField.exists_valuationSubring_forall_map_mem_iff_valuation_le_one
    (F : Type) [Field F] [NumberField F] (σ : F →+* AlgebraicClosure ℚ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ B : ValuationSubring (AlgebraicClosure ℚ), ∀ x : F, σ x ∈ B ↔ v.valuation F x ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one.solution
