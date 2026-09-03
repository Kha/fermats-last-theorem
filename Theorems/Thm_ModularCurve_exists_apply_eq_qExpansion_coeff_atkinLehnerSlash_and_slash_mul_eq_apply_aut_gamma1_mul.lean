import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Even k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (ι : L →+* ℂ) (s : L ≃ₐ[ℚ] L) (b : ℕ) (hb : Nat.Coprime b p) (hs : s ζ = ζ ^ b)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hδp : ((δ 0 0 : ℤ) : ZMod p) = (b : ZMod p)) (hδM : ((δ 0 0 : ℤ) : ZMod M) = 1) (n : ℕ) :
    ∃ z : L, ι z = (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∧
      (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n = ι (s z) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul.solution
