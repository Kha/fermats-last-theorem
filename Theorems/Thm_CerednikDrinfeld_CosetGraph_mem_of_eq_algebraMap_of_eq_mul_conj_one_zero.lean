import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_mem_of_eq_algebraMap_of_eq_mul_conj_one_zero
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open scoped Classical

theorem CerednikDrinfeld.CosetGraph.mem_of_eq_algebraMap_of_eq_mul_conj_one_zero

    {a₂ b₂ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₂ : IsDefiniteRamifiedExactlyAt a₂ b₂ q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (Γ : Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (z : (ℍ[ℚ, a₂, b₂])ˣ) (hz : ∃ c : ℚ, c ≠ 0 ∧ (z : ℍ[ℚ, a₂, b₂]) = algebraMap ℚ (ℍ[ℚ, a₂, b₂]) c)
    (hprod : ∃ δ ∈ Γ, ∃ γ ∈ Γ, ∃ t : (ℍ[ℚ, a₂, b₂])ˣ, z = δ * (t⁻¹ * γ * t)) :
    z ∈ Γ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_mem_of_eq_algebraMap_of_eq_mul_conj_one_zero.solution
