import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import P2M.Util
import P2M.Sol.S_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_mul_lt

set_option autoImplicit false

theorem RegularSingular.eq_zero_of_norm_le_mul_rpow_of_mul_lt
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (A : Fin d → ((Fin r → E) →L[ℂ] (Fin r → E))) (L : ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ L) (hA : ∀ k, ‖A k‖ ≤ L)
    (σ : ℝ) (hσ : (r + d) * L < σ)
    (F F' : ℝ → (Fin r → E))
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
      (y : ℂ) • F' y = (fun i => ∑ j, M i j • F y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y))
    (B : ℝ) (hB : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ σ) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1, F y = 0 := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_mul_lt.solution
