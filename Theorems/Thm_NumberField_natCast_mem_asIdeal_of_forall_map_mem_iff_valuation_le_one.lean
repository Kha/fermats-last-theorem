import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
    (K : Type) [Field K] [NumberField K] {Ω : Type} [Field Ω]
    (σ : K →+* Ω) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ x : K, σ x ∈ A ↔ v.valuation K x ≤ 1)
    (p : ℕ) (hp : A.valuation (σ (p : K)) < 1) :
    ((p : ℤ) : 𝓞 K) ∈ v.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one.solution
