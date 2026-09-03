import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ F : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F : UpperHalfPlane → ℂ) = fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul.solution
