import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff
    (A : Type) [NormedField A] [NormedAlgebra ℝ A]
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1)) ∧ IsUnit (Matrix.det (Matrix.of q.2.1))}) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    IsFiniteMeasureOnCompacts μA →
    ∃ F : (Fin 2 → Fin 2 → A) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
        ∀ (g : GL (Fin 2) A) (p : P),
          F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) A), p) =
            ∫ h, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
              Matrix.of.symm ((h⁻¹ * g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A), p) ∂μA := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff.solution
