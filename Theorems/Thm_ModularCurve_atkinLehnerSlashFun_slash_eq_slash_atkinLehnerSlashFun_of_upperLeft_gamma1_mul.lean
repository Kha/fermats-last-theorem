import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (d d' : ℕ) (hd : d.Coprime (M * p)) (hd' : d'.Coprime (M * p))
    (hdM : (d' : ZMod M) = (d : ZMod M)) (hdp : (d' : ZMod p) * (d : ZMod p) = 1)
    (δ δ' : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p)) (hδ' : δ' ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hδ00 : ((δ 0 0 : ℤ) : ZMod (M * p)) = (d : ZMod (M * p)))
    (hδ'00 : ((δ' 0 0 : ℤ) : ZMod (M * p)) = (d' : ZMod (M * p))) :
    (fun τ : UpperHalfPlane => (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) =
      ((fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∣[k] δ') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul.solution
