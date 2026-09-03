import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant

set_option autoImplicit false
open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant
    (N : ℕ) [NeZero N] (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ δ ∈ CongruenceSubgroup.Gamma N, ∀ τ : UpperHalfPlane, G (δ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N) (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (γ γ' : SL(2, ℤ))
    (hγγ' : !![(1 : ZMod N), 0; 0, (s : ZMod N)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) * !![(1 : ZMod N), 0; 0, (s : ZMod N)])
    (n : ℕ) :
    ∃ z : ↥K, (z : ℂ) = (UpperHalfPlane.qExpansion N
        ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n ∧
      (UpperHalfPlane.qExpansion N
        ((fun τ : UpperHalfPlane => G (γ' • τ)) * ModularForm.discriminant ^ m)).coeff n = φ z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant.solution
