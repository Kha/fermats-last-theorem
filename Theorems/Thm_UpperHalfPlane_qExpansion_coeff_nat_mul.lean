import Mathlib.NumberTheory.ModularForms.QExpansion
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_nat_mul

open UpperHalfPlane
open scoped Manifold
theorem UpperHalfPlane.qExpansion_coeff_nat_mul {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ} (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h) (hhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) {M : ℕ} (hM : 0 < M) (n : ℕ) : (qExpansion (M * h) F).coeff n = if M ∣ n then (qExpansion h F).coeff (n / M) else 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_qExpansion_coeff_nat_mul.solution
