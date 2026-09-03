import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_one_splitTransform_eq

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_one_splitTransform_eq
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ),
      (∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, I (fun x => a * f x + b * g x) = fun M => a * I f M + b * I g M) ∧
      ∀ H : ℝ × ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H → tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0} →
        (∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) →
        (∀ (a₁ a₂ : ℝ) (p : P), H (-a₁, -a₂, p) = -H (a₁, a₂, p)) →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        HasCompactSupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ⊆
          {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
        (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
          entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p
              ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
            ((archWeightCharℝ 1 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 1 k₂ : ℂˣ) : ℂ) *
              entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p g) ∧
        ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
          splitTransform
              (entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p)
              a₁ a₂ =
            H (a₁, a₂, p) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_one_splitTransform_eq.solution
