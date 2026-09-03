import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Util
import P2M.Sol.S_ModularCurve_qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven (p : ℕ) [Fact p.Prime] (t : ℕ → ℤ) (ht : ∀ n : ℕ, (t n : ℂ) = ModularFormClass.qCoeff ModularForm.discriminant n) : t (p ^ 2) = t p ^ 2 - (p : ℤ) ^ 11 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven.solution
