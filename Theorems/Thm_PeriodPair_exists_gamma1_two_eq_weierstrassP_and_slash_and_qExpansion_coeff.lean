import Mathlib
import P2M.Util
import P2M.Sol.S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff

set_option autoImplicit false

open scoped MatrixGroups ModularForm Real Matrix

theorem PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
    (M : ℕ) [NeZero M] :
    ∃ W : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ (L : UpperHalfPlane → PeriodPair),
        (∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
        ∀ (t : ZMod M) (τ : UpperHalfPlane),
          W t τ = 12 * ((2 * π * Complex.I) ^ 2)⁻¹ * (L τ).weierstrassP ((t.val : ℂ) / M)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(W t) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (t * ((γ 1 1 : ℤ) : ZMod M)))) ∧
      ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (UpperHalfPlane.qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * Complex.exp (2 * π * Complex.I / M) ^ t.val /
              (1 - Complex.exp (2 * π * Complex.I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (Complex.exp (2 * π * Complex.I / M) ^ (t.val * d) +
                  (Complex.exp (2 * π * Complex.I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.solution
