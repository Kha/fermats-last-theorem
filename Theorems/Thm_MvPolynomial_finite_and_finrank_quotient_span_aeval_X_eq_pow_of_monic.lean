import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic

universe u v

theorem MvPolynomial.finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic
    (k : Type u) [Field k] (ι : Type v) [Finite ι] (f : Polynomial k) (hf : f.Monic) :
    Module.Finite k (MvPolynomial ι k ⧸
        Ideal.span (Set.range fun i : ι => Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι k) f)) ∧
      Module.finrank k (MvPolynomial ι k ⧸
        Ideal.span (Set.range fun i : ι => Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι k) f)) =
        f.natDegree ^ Nat.card ι := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic.solution
