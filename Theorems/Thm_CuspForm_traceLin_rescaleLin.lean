import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_traceLin_rescaleLin
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

set_option autoImplicit false
open CongruenceSubgroup ModularForm FreyPackage.ModMCarrier
theorem CuspForm.traceLin_rescaleLin {M q' : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q') (hq : q'.Prime) (hqR : ¬ q' ∣ W.R)
    (f : CuspForm (Gamma0 W.R) 2) :
    haveI : NeZero W.R := ⟨fun h => absurd (h ▸ Nat.dvd_zero q') hqR⟩
    CuspForm.traceLin W hq (rescaleLin W.q_mul_R_dvd 2 f)
      = CuspForm.heckeTLin 2 hq hqR f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_traceLin_rescaleLin.solution
