import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq
    {a₁ b₁ : ℚ} (R₀ R' : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₀ : IsOrder R₀) (hR' : IsOrder R')
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.localBox R' w = Submodule.localBox R₀ w) :
    (∀ x : (ℍ[ℚ, a₁, b₁])ˣ,
        x ∈ CerednikDrinfeld.CosetGraph.awayUnits R' v ↔
          ∃ K K' : ℕ, ((r ^ K : ℕ) : ℚ) • ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₀ ∧
            ((r ^ K' : ℕ) : ℚ) • ((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₀) ∧
    (∀ y : ↥R', ∃ K : ℕ, ((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) ∈ R₀) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq.solution
