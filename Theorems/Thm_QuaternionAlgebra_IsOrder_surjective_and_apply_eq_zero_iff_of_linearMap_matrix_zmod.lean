import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (N : ℕ) [NeZero N]
    (φ ψ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]))
    (hψ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ψ ⟨1, h⟩ = 1)
    (hψmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ψ x * ψ y) :
    Function.Surjective ψ ∧
      ∀ x : ↥Λ, ψ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod.solution
