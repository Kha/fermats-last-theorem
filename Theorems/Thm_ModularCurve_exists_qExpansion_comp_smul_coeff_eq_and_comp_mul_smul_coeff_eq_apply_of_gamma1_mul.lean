import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_comp_mul_smul_coeff_eq_apply_of_gamma1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm Manifold in

theorem ModularCurve.exists_qExpansion_comp_smul_coeff_eq_and_comp_mul_smul_coeff_eq_apply_of_gamma1_mul
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ)
    (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 (M * p), ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))})
    (b : ℕ) (hb : Nat.Coprime b p) (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) ^ b)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hδp : ((δ 0 0 : ℤ) : ZMod p) = (b : ZMod p)) (hδM : ((δ 0 0 : ℤ) : ZMod M) = 1) (n : ℕ) :
    ∃ z : ↥K, (z : ℂ) = (UpperHalfPlane.qExpansion p
        ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n ∧
      (UpperHalfPlane.qExpansion p
        ((fun τ : UpperHalfPlane => G ((δ * γ) • τ)) * ModularForm.discriminant ^ m)).coeff n = φ z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_comp_mul_smul_coeff_eq_apply_of_gamma1_mul.solution
