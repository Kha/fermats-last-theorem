import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_forall_exists_pow_smul_conj_mem_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_mem_asIdeal

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "IsDedekindDomain NumberField QuaternionAlgebra~IsEichlerOrder"

theorem Submodule.forall_exists_pow_smul_conj_mem_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_mem_asIdeal
    {a b : ℚ} (R R' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R')
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (γ₀ : (ℍ[ℚ, a, b])ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hconj : Submodule.conjByFiniteIdele R' (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀ * g) = R) :
    (∀ x : ↥R, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) * ((γ₀ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ∈ R') ∧
    (∀ y : ↥R', ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((γ₀ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) * ((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ∈ R) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_forall_exists_pow_smul_conj_mem_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_mem_asIdeal.solution
