import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod

universe u v

theorem MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod
    (k : Type u) [CommRing k] [Nontrivial k] {ι : Type v} [Fintype ι] (N : ι → ℕ) :
    Module.finrank k (MvPolynomial ι k ⧸
      Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι k) ^ N i)) = ∏ i, N i := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod.solution
