import Mathlib.FieldTheory.Separable
import P2M.Util
import P2M.Sol.S_Polynomial_exists_forall_not_isRoot_of_weighted

open Polynomial
theorem Polynomial.exists_forall_not_isRoot_of_weighted (n w : ℕ) (F : Polynomial (Polynomial ℚ)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (hlead : (F.coeff n).coeff 0 ≠ 0) (hsep : (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k : Polynomial ℚ).Separable) (hroot : ∀ g : Polynomial ℚ, F.eval g ≠ 0) (M : ℕ) (hM : M ≠ 0) (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧ ∀ x : ℚ, ¬ (F.map (Polynomial.evalRingHom ((M : ℚ) * m))).IsRoot x := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_forall_not_isRoot_of_weighted.solution
