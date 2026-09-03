import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import P2M.Util
import P2M.Sol.S_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin

set_option autoImplicit false

open CongruenceSubgroup

theorem FreyPackage.ModMCarrier.rescaleLin_eq_levelInclusionLin {R M : ℕ} [NeZero M]
    (h : 1 * R ∣ M) (hRM : R ∣ M) (k : ℤ) (f : CuspForm (Gamma0 R) k) :
    FreyPackage.ModMCarrier.rescaleLin h k f = FreyPackage.ModMCarrier.levelInclusionLin hRM k f := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin.solution
