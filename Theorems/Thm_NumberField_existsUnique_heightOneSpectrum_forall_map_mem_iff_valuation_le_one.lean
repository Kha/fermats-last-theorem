import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
    (K : Type) [Field K] [NumberField K] {Ω : Type} [Field Ω]
    (σ : K →+* Ω) (A : ValuationSubring Ω) (hA : ∃ x : K, σ x ∉ A) :
    ∃! v : HeightOneSpectrum (𝓞 K), ∀ x : K, σ x ∈ A ↔ v.valuation K x ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one.solution
