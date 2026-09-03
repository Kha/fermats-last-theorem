import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsOrder.exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (V : Type) [AddCommGroup V] [Module ℂ V] (hV : Module.finrank ℂ V = 2)
    (ρ : ↥Λ → (V →ₗ[ℂ] V))
    (hρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id)
    (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (hρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y) :
    ∃ P : V ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ (x : ↥Λ) (v : V),
      P (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (P v) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two.solution
