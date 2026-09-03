import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_smul_eq_qmPeriodLattice_smul_and_smul_eq_qmPeriodMap_mul_of_mem_fuchsianGroup

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
p2m_open "QuaternionAlgebra~denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq CerednikDrinfeld"

theorem QuaternionAlgebra.IsEichlerOrder.exists_smul_eq_qmPeriodLattice_smul_and_smul_eq_qmPeriodMap_mul_of_mem_fuchsianGroup
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L M : Submodule ℤ (Fin 2 → ℂ)) (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0)
    (hL : c • L = qmPeriodLattice ι Λ τ)
    (hlev : (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
        ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam ∈ c • M → ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r) ∈ c • M))
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ fuchsianGroup R ι)
    (m : ℕ) (v : Fin 2 → ℂ) (ξ₀ : ℍ[ℚ, a, b]) (hξ₀ : ξ₀ ∈ Λ)
    (hfull : c • v = ((m : ℂ)⁻¹) • qmPeriodMap ι τ ξ₀) :
    ∃ (c' : ℂ) (u w : ℍ[ℚ, a, b]), c' ≠ 0 ∧ u ∈ R ∧ w ∈ R ∧ u * w = 1 ∧ w * u = 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = ι u ∧
      c' • L = qmPeriodLattice ι Λ (γ • τ) ∧
      (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
        ((N : ℂ)⁻¹) • qmPeriodMap ι (γ • τ) lam ∈ c' • M → ((N : ℂ)⁻¹) • qmPeriodMap ι (γ • τ) (lam * r) ∈ c' • M) ∧
      c' • v = ((m : ℂ)⁻¹) • qmPeriodMap ι (γ • τ) (ξ₀ * w) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_smul_eq_qmPeriodLattice_smul_and_smul_eq_qmPeriodMap_mul_of_mem_fuchsianGroup.solution
