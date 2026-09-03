import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_eq_smul_one_of_forall_mem_awayUnits_commute
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain CerednikDrinfeld

theorem QuaternionAlgebra.exists_eq_smul_one_of_forall_mem_awayUnits_commute
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (K₀ : Type) [Field K₀] [CharZero K₀]
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀) :
    ∀ g : Matrix (Fin 2) (Fin 2) K₀,
      (∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v →
        g * ι₀ (x : ℍ[ℚ, a₁, b₁]) = ι₀ (x : ℍ[ℚ, a₁, b₁]) * g) →
      ∃ c : K₀, g = c • (1 : Matrix (Fin 2) (Fin 2) K₀) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_eq_smul_one_of_forall_mem_awayUnits_commute.solution
