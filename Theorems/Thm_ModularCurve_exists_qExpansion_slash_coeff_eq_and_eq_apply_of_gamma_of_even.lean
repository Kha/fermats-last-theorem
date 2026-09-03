import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even
    (N : ℕ) [NeZero N] {k : ℤ} (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion N F).coeff n = (r : ℂ))
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N) (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (γ γ' : SL(2, ℤ))
    (hγγ' : !![(1 : ZMod N), 0; 0, (s : ZMod N)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) * !![(1 : ZMod N), 0; 0, (s : ZMod N)])
    (n : ℕ) :
    ∃ z : ↥K, (z : ℂ) = (UpperHalfPlane.qExpansion N ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n ∧
      (UpperHalfPlane.qExpansion N ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ')).coeff n = φ z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even.solution
