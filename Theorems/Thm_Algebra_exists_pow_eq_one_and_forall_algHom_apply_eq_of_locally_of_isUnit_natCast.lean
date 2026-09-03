import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast

set_option autoImplicit false

universe u

theorem Algebra.exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast
    (A₀ : Type u) [CommRing A₀] (B : Type u) [CommRing B] [Algebra A₀ B] (n : ℕ) (hn : IsUnit ((n : ℕ) : B))
    (v : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω], (B →ₐ[A₀] Ω) → Ω)
    (hloc : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ∃ f : B, f ∉ 𝔭 ∧ ∃ ε : Localization.Away f, ε ^ n = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : Localization.Away f →ₐ[A₀] Ω),
        v Ω (φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away f))) = φ ε) :
    ∃ ε : B, ε ^ n = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : B →ₐ[A₀] Ω), v Ω φ = φ ε := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast.solution
