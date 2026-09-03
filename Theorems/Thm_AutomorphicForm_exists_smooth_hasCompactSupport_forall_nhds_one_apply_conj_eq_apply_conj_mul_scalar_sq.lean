import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq

set_option autoImplicit false

open MeasureTheory AutomorphicForm

theorem AutomorphicForm.exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (d : ℝˣ) :
    ∃ g : GL (Fin 2) ℝ → ℂ,
      ((∃ G : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
        ∀ s, g s = G (fun i j => (s : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport g) ∧
      ∃ U ∈ nhds (1 : GL (Fin 2) ℝ), ∀ t ∈ U, ∀ h : GL (Fin 2) ℝ,
        g (h⁻¹ * t * h) =
          f (h⁻¹ * (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) * h) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq.solution
