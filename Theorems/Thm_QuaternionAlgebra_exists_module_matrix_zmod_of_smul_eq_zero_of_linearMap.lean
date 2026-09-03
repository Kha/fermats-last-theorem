import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap

set_option autoImplicit false

universe u

open scoped Quaternion

theorem QuaternionAlgebra.exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hmul : ∀ x y : ↥Λ, (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    (V : Type u) [AddCommGroup V] (hV : ∀ v : V, ℓ • v = 0)
    (act : ↥Λ → V →+ V)
    (hact1 : act ⟨1, h1⟩ = AddMonoidHom.id V)
    (hactmul : ∀ x y : ↥Λ, act ⟨_, hmul x y⟩ = (act x).comp (act y))
    (hactadd : ∀ x y : ↥Λ, act (x + y) = act x + act y) :
    ∃ inst : Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V,
      ∀ (m : ↥Λ) (v : V), @HSMul.hSMul (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V V (@instHSMul _ _ inst.toSMul) (φ m) v = act m v := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_module_matrix_zmod_of_smul_eq_zero_of_linearMap.solution
