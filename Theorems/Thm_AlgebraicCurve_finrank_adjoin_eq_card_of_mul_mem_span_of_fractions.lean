import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finrank_adjoin_eq_card_of_mul_mem_span_of_fractions

set_option autoImplicit false

open Polynomial

universe u v

theorem AlgebraicCurve.finrank_adjoin_eq_card_of_mul_mem_span_of_fractions
    {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E] {n : ℕ}
    (y : E) (s : Fin n → E)
    (hmul : ∀ i j, ∃ c : Fin n → k[X], s i * s j = ∑ l, Polynomial.aeval y (c l) * s l)
    (hind : ∀ c : Fin n → k[X], ∑ i, Polynomial.aeval y (c i) * s i = 0 → c = 0)
    (hfrac : ∀ z : E, ∃ cu cv : Fin n → k[X],
      ∑ i, Polynomial.aeval y (cv i) * s i ≠ 0 ∧
        z * ∑ i, Polynomial.aeval y (cv i) * s i = ∑ i, Polynomial.aeval y (cu i) * s i) :
    FiniteDimensional (IntermediateField.adjoin k ({y} : Set E)) E ∧
      Module.finrank (IntermediateField.adjoin k ({y} : Set E)) E = n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finrank_adjoin_eq_card_of_mul_mem_span_of_fractions.solution
