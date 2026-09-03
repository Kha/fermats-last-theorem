import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import P2M.Util
import P2M.Sol.S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq

set_option autoImplicit false

open scoped SchwartzMap

theorem SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (ι : Type) [Fintype ι] :
    ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
      g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq.solution
