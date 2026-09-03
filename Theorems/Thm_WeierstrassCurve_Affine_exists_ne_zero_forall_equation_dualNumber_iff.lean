import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff

set_option autoImplicit false

universe u

open TrivSqZeroExt

theorem WeierstrassCurve.Affine.exists_ne_zero_forall_equation_dualNumber_iff
    {k : Type u} [Field k] (W : WeierstrassCurve.Affine k) (hΔ : W.Δ ≠ 0)
    (x₀ y₀ : k) (h₀ : W.Equation x₀ y₀) :
    ∃ v : k × k, v ≠ 0 ∧
      ∀ x y : DualNumber k, x.fst = x₀ → y.fst = y₀ →
        ((W.map (algebraMap k (DualNumber k))).Equation x y ↔ ∃ c : k, x.snd = c * v.1 ∧ y.snd = c * v.2) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff.solution
