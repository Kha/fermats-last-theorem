import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Matrix.Notation
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable

set_option autoImplicit false

theorem
LanglandsTunnell.CubicInduction.exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
    (j : Fin 3) (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) [FiniteDimensional ℂ E]
    (hne : ∃ F ∈ E, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0)
    (hstab : ∀ F ∈ E, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ, (fun r => F (r * r₀)) ∈ E) :
    let rot : Fin 3 → Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun c₁ c₂ s => Matrix.of fun i k =>
      if i = c₁ ∧ k = c₁ then Real.cos s else if i = c₂ ∧ k = c₂ then Real.cos s else
      if i = c₁ ∧ k = c₂ then - Real.sin s else if i = c₂ ∧ k = c₁ then Real.sin s else
      if i = k then (1 : ℝ) else 0
    let planes : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]
    let val : E → Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun F => (F : Matrix (Fin 3) (Fin 3) ℝ → ℂ)
    let realise : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun q => MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q
    ∀ L : Fin 3 → Module.End ℂ E,
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0) →
      (∀ (F : E), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        val (L 0 (L 1 F)) r - val (L 1 (L 0 F)) r = val (L 2 F) r ∧
        val (L 0 (L 2 F)) r - val (L 2 (L 0 F)) r = - val (L 1 F) r ∧
        val (L 1 (L 2 F)) r - val (L 2 (L 1 F)) r = val (L 0 F) r) →
      ∃ (α : Fin 2) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ), p ≠ 0 ∧
      p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
      ∃ F ∈ E, ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        F r = ((r.det : ℝ) : ℂ) ^ (α : ℕ) *
          MvPolynomial.eval (fun ab : Fin 3 × Fin 3 => ((r ab.1 ab.2 : ℝ) : ℂ)) (realise p) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.solution
