import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import P2M.Util
import P2M.Sol.S_ExtCitation_extVanishingCts_of_three_le
attribute [-instance] ExtCitation.Cyclotomic.instIsCycExt JacobiSumStickelberger.instModuleZModModP
attribute [-simp] ExtCitation.Cyclotomic.unitsEnd_proj galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj Stickelberger.mem_exponentSet

theorem ExtCitation.extVanishingCts_of_three_le {p : ℕ} [Fact p.Prime] (h3 : 3 ≤ p) :
    ExtCitation.ExtVanishingCts p := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_extVanishingCts_of_three_le.solution
