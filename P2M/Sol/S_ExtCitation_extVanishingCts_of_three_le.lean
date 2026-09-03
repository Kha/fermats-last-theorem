import Theorems.Thm_ExtCitation_extVanishingCts_three
import Theorems.Thm_ExtCitation_extVanishingCts_of_five_le
import P2M.Util
namespace P2MW.S_ExtCitation_extVanishingCts_of_three_le
attribute [-instance] ExtCitation.Cyclotomic.instIsCycExt JacobiSumStickelberger.instModuleZModModP
attribute [-simp] ExtCitation.Cyclotomic.unitsEnd_proj galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj Stickelberger.mem_exponentSet

theorem solution {p : ℕ} [hp : Fact p.Prime] (h3 : 3 ≤ p) : ExtCitation.ExtVanishingCts p := by
  rcases Nat.lt_or_ge p 5 with h | h
  · have h4 : p ≠ 4 := fun h4 => by
      subst h4
      exact absurd hp.out (by decide)
    have hp3 : p = 3 := by omega
    subst hp3
    exact ExtCitation.extVanishingCts_three
  · exact ExtCitation.extVanishingCts_of_five_le p h
