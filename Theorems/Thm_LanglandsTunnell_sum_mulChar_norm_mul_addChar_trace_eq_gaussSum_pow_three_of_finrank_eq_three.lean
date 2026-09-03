import Mathlib.NumberTheory.GaussSum
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_sum_mulChar_norm_mul_addChar_trace_eq_gaussSum_pow_three_of_finrank_eq_three

set_option autoImplicit false

theorem LanglandsTunnell.sum_mulChar_norm_mul_addChar_trace_eq_gaussSum_pow_three_of_finrank_eq_three
    (F : Type) [Field F] [Fintype F] (F' : Type) [Field F'] [Algebra F F'] [Fintype F']
    (h3 : Module.finrank F F' = 3) (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) :
    ∑ y : F', χ (Algebra.norm F y) * ψ (Algebra.trace F F' y) = (gaussSum χ ψ) ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_sum_mulChar_norm_mul_addChar_trace_eq_gaussSum_pow_three_of_finrank_eq_three.solution
