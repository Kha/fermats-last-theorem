import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq

set_option autoImplicit false

open QuaternionAlgebra
open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_zmod_prod_section_of_relIndex_eq_sq
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ ρ : ZMod ℓ × ZMod ℓ → ↥Λ,
      (∀ v, ((ρ v : ↥Λ) : ℍ[ℚ, a, b]) ∈ L₀) ∧
      (∀ v w, ∃ y : ↥Λ,
        ((ρ (v + w) : ↥Λ) : ℍ[ℚ, a, b]) - (ρ v : ℍ[ℚ, a, b]) - (ρ w : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        ∃ v, ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (ρ v : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ v w, (∃ y : ↥Λ, ((ρ v : ↥Λ) : ℍ[ℚ, a, b]) - (ρ w : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) → v = w) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq.solution
