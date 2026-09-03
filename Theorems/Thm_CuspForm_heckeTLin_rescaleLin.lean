import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_heckeTLin_rescaleLin

theorem CuspForm.heckeTLin_rescaleLin {R M d ℓ : ℕ} [NeZero M] (hdRM : d * R ∣ M)
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓR : ¬ ℓ ∣ R)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) :
    CuspForm.heckeTLin 2 hℓ hℓM (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)
      = FreyPackage.ModMCarrier.rescaleLin hdRM 2 (CuspForm.heckeTLin 2 hℓ hℓR f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeTLin_rescaleLin.solution
