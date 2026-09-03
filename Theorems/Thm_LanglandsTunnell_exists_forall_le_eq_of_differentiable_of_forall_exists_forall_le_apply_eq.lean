import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_le_eq_of_differentiable_of_forall_exists_forall_le_apply_eq

set_option autoImplicit false

theorem LanglandsTunnell.exists_forall_le_eq_of_differentiable_of_forall_exists_forall_le_apply_eq
    (f : ℤ → ℂ → ℂ) (hf : ∀ c : ℤ, Differentiable ℂ (f c))
    (h : ∀ z : ℂ, ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → f c z = f c₀ z) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → f c = f c₀ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_le_eq_of_differentiable_of_forall_exists_forall_le_apply_eq.solution
