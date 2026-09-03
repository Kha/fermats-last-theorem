import Mathlib.Analysis.Matrix.Normed
import P2M.Util
import P2M.Sol.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite

theorem Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ),
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℝ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℝ) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.solution
