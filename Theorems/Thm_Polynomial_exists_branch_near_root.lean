import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import P2M.Util
import P2M.Sol.S_Polynomial_exists_branch_near_root

open Polynomial
theorem Polynomial.exists_branch_near_root {n w : ℕ} (F : Polynomial (Polynomial ℂ)) (hF : F.natDegree ≤ n) (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : ℂ) (hc : c ≠ 0) (hlead : F.coeff n = C c) (P : Fin n → Polynomial ℂ) (hP : ∀ i, (P i).natDegree ≤ w) (hPinj : Function.Injective fun i => (P i).coeff w) (hR : ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0) : ∃ C₀ T : ℝ, 0 < C₀ ∧ ∀ t : ℂ, T ≤ ‖t‖ → ∀ x : ℂ, (F.map (Polynomial.evalRingHom t)).IsRoot x → ∃ i, ‖x - (P i).eval t‖ ≤ C₀ / ‖t‖ := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_branch_near_root.solution
