import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq
    (N : ℕ) [NeZero N] (k : ℤ) (F : ℕ → CuspForm (Gamma N) k)
    (hF : ∀ p ∈ N.primeFactors,
      (⇑(F p) : UpperHalfPlane → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) = ⇑(F p))
    (hsum : ∀ γ ∈ Gamma1 N,
      (⇑(∑ p ∈ N.primeFactors, F p) : UpperHalfPlane → ℂ) ∣[k] γ =
        ⇑(∑ p ∈ N.primeFactors, F p)) :
    ∃ G : ℕ → CuspForm (Gamma N) k,
      (∀ p ∈ N.primeFactors, ∀ γ ∈ Gamma1 (N / p),
        (⇑(G p) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(G p)) ∧
      ∑ p ∈ N.primeFactors, G p = ∑ p ∈ N.primeFactors, F p := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.solution
