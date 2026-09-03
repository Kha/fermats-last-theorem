import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Algebra.Rat
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_pow_eq_of_kummer_descent

theorem ValuationSubring.exists_pow_eq_of_kummer_descent
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [IsGalois K L] [CharZero L]
    (P : ValuationSubring L) (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P)
    (p q : ℕ) (hp : p.Prime) (hqp : q.Prime) (hpq : p ≠ q)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P)
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    (hroot : ∀ k : ℕ, ∃ r : K, r ^ (p ^ k) = (q : K))
    (hres : ∀ u : P.comap (algebraMap K L), IsUnit u →
      ∃ z : P.comap (algebraMap K L), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)))
    (a : K) (ha : a ≠ 0) : ∃ b : K, b ^ p = a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_pow_eq_of_kummer_descent.solution
