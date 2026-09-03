import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_mem_of_eq_algebraMap_of_eq_mul_conj
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open scoped Classical

theorem CerednikDrinfeld.CosetGraph.mem_of_eq_algebraMap_of_eq_mul_conj

    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (Γ : Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : ∃ c : ℚ, c ≠ 0 ∧ (z : ℍ[ℚ, a₁, b₁]) = algebraMap ℚ (ℍ[ℚ, a₁, b₁]) c)
    (hprod : ∃ δ ∈ Γ, ∃ γ ∈ Γ, ∃ t : (ℍ[ℚ, a₁, b₁])ˣ, z = δ * (t⁻¹ * γ * t)) :
    z ∈ Γ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_mem_of_eq_algebraMap_of_eq_mul_conj.solution
