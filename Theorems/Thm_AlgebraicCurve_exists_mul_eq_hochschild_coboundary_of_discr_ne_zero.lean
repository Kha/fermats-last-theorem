import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero

set_option autoImplicit false

open Polynomial

universe u v

theorem AlgebraicCurve.exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (hdisc : Algebra.discr K[X] b ≠ 0)
    (ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hψ1 : ∀ j k, ψ 0 j k = 0) (hψc : ∀ i j k, ψ i j k = ψ j i k)
    (hψa : ∀ i j l m, (∑ k, ψ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * ψ k l m) +
        (∑ k, b.repr (b j * b l) k * ψ i k m) - (∑ k, ψ i j k * b.repr (b k * b l) m) = 0) :
    ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
      ∀ i j m, u * ψ i j m = (∑ k, lam j k * b.repr (b i * b k) m) -
        (∑ k, b.repr (b i * b j) k * lam k m) + (∑ k, lam i k * b.repr (b k * b j) m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero.solution
