import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_finset_forall_smul_eq_of_nrd_eq_of_not_isSquare

set_option autoImplicit false

open scoped MatrixGroups Topology TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld
theorem CerednikDrinfeld.exists_finset_forall_smul_eq_of_nrd_eq_of_not_isSquare
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (ν : ℤ) (hν : 0 < ν) (hsq : ¬ IsSquare ν) :
    ∃ F : Finset UpperHalfPlane,
      ∀ (τ : UpperHalfPlane) (α : ℍ[ℚ, a, b]) (g : GL (Fin 2) ℝ),
        α ∈ Λ → nrd α = (ν : ℚ) → (g : Matrix (Fin 2) (Fin 2) ℝ) = ι α → g • τ = τ →
          ∃ γ ∈ fuchsianGroup Λ ι, ∃ τ₀ ∈ F, γ • τ₀ = τ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_finset_forall_smul_eq_of_nrd_eq_of_not_isSquare.solution
