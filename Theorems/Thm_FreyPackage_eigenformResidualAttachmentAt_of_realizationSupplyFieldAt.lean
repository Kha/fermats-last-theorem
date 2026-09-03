import Definitions.Def_FreyPackage_EigenformRealizationSupplyField
import Definitions.Def_FreyPackage_EigenformResidualAttachment
import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt

theorem FreyPackage.eigenformResidualAttachmentAt_of_realizationSupplyFieldAt (P : FreyPackage) (M : ℕ) [NeZero M] :
    letI := ModularCurve.heckeModuleBar M; ModularCurve.FrobeniusQuadraticConcrete M P.p → P.EigenformRealizationSupplyFieldAt M → P.EigenformResidualAttachmentAt M := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.solution
