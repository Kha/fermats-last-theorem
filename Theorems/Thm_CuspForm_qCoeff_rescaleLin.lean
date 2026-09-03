import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_rescaleLin

set_option autoImplicit false
open CongruenceSubgroup

theorem CuspForm.qCoeff_rescaleLin
    {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM k f) n
      = if d ∣ n then (d : ℂ) ^ (k - 1) * ModularFormClass.qCoeff f (n / d) else 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_rescaleLin.solution
