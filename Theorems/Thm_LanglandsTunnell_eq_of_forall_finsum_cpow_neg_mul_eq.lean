import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Finprod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_eq_of_forall_finsum_cpow_neg_mul_eq

set_option autoImplicit false

theorem LanglandsTunnell.eq_of_forall_finsum_cpow_neg_mul_eq
    (N : ℕ) (hN : 1 < N) (a b : ℤ → ℂ)
    (ha : (Function.support a).Finite) (hb : (Function.support b).Finite)
    (h : ∀ u : ℂ, ∑ᶠ i : ℤ, (N : ℂ) ^ (-(i : ℂ) * u) * a i = ∑ᶠ i : ℤ, (N : ℂ) ^ (-(i : ℂ) * u) * b i) :
    a = b := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_eq_of_forall_finsum_cpow_neg_mul_eq.solution
