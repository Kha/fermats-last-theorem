import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_le_span_and_eq_bot_of_signType_of_isHomogeneous

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.le_span_and_eq_bot_of_signType_of_isHomogeneous
    (ε : Fin 3 → Fin 2) (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hS : (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0))
    (hsign : (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p))
    (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀) :
    ((ε 0 = ε b₀ ∧ ε 0 = ε c₀) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2}) ∧
    ((ε 0 = ε b₀ ∧ ε 0 ≠ ε c₀) →
      S 0 = ⊥ ∧
          S 1 ≤ Submodule.span ℂ {(MvPolynomial.X c₀ : MvPolynomial (Fin 3) ℂ)} ∧
          S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X b₀ : MvPolynomial (Fin 3) ℂ)}) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_le_span_and_eq_bot_of_signType_of_isHomogeneous.solution
