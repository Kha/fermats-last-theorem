import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpansion_coeff_atkinLehnerSlash_eq_and_slash_mul_eq_apply_gamma1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_qExpansion_coeff_atkinLehnerSlash_eq_and_slash_mul_eq_apply_gamma1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Even k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))})
    (b : ℕ) (hb : Nat.Coprime b p) (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) ^ b)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hδp : ((δ 0 0 : ℤ) : ZMod p) = (b : ZMod p)) (hδM : ((δ 0 0 : ℤ) : ZMod M) = 1) (n : ℕ) :
    ∃ z : ↥K, (z : ℂ) = (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∧
      (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n = φ z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpansion_coeff_atkinLehnerSlash_eq_and_slash_mul_eq_apply_gamma1_mul.solution
