import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_ne_and_le_span_X_of_signType_one_of_odd

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_ne_and_le_span_X_of_signType_one_of_odd
    (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ε : Fin 3 → Fin 2) (hodd : ε 0 ≠ ε b₀)
    (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hS : (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0))
    (hsign : (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p)) :
    ∃ m : Fin 3, m ≠ c₀ ∧ S 1 ≤ Submodule.span ℂ {(MvPolynomial.X m : MvPolynomial (Fin 3) ℂ)} ∧
      (1 + ∑ a : Fin 3, (ε a : ℕ)) % 2 = (ε c₀ : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_and_le_span_X_of_signType_one_of_odd.solution
