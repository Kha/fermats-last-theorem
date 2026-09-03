import Mathlib
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix
import P2M.Util
namespace P2MW.S_CuspForm_traceLin_rescaleLin

set_option autoImplicit false
open CongruenceSubgroup ModularForm FreyPackage.ModMCarrier

theorem solution {M q' : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q') (hq : q'.Prime) (hqR : ¬ q' ∣ W.R)
    (f : CuspForm (Gamma0 W.R) 2) :
    haveI : NeZero W.R := ⟨fun h => absurd (h ▸ Nat.dvd_zero q') hqR⟩
    CuspForm.traceLin W hq (rescaleLin W.q_mul_R_dvd 2 f)
      = CuspForm.heckeTLin 2 hq hqR f := by
  exact CuspForm.traceLin_of_coe_eq_slash_heckeDiagMatrix W hq (coe_rescaleLin_apply W.q_mul_R_dvd 2 f)
