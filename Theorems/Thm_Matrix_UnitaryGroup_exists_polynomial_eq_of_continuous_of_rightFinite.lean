import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import P2M.Util
import P2M.Sol.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite

theorem Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.solution
