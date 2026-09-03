import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow

set_option autoImplicit false

universe u v

theorem MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow
    (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Finite ∧
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Flat ∧
    ∀ q : PrimeSpectrum (MvPolynomial σ R),
      (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.finrank q = p ^ Nat.card σ := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow.solution
