import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import P2M.Util
import P2M.Sol.S_Polynomial_exists_approximants_at_infty

open Polynomial
theorem Polynomial.exists_approximants_at_infty {K : Type*} [Field K] (n w : ℕ) (F : Polynomial (Polynomial K)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : K) (hlead : F.coeff n = C c) (r : Fin n → K) (hr : Function.Injective r) (h0 : ∀ i, (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k).eval (r i) = 0) (h1 : ∀ i, (derivative (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k)).eval (r i) ≠ 0) : ∃ P : Fin n → Polynomial K, (∀ i, (P i).natDegree ≤ w) ∧ (∀ i, (P i).coeff w = r i) ∧ ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_approximants_at_infty.solution
