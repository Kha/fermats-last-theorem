import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_rescaleLin_apply

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodMap_rescaleLin_apply
    {R M d : ℕ} [NeZero R] [NeZero M] [NeZero d] (hdRM : d * R ∣ M)
    (h : CohCarrier.LevelLE R M ⊤ ⊤ d)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (γ : ↥(CohCarrier.GammaH M ⊤)) :
    ModularCurve.periodMap M (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)
        (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) =
      ModularCurve.periodMap R f
        (Additive.ofMul ⟨(CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)),
          CohCarrier.GammaH_le_Gamma0 ⊤ (CohCarrier.iotaDeg R M ⊤ ⊤ d h γ).2⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_rescaleLin_apply.solution
