import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyCurve_four_dvd_card_reductionMod
import Theorems.Thm_WeierstrassCurve_card_pos
import Theorems.Thm_WeierstrassCurve_card_le_two_mul_add_one
import P2M.Util
namespace P2MW.S_FreyCurve_freyCurveInt_apOfModel_three

open WeierstrassCurve FreyPackage

theorem solution (P : FreyPackage)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor 3) :
    (FreyPackage.freyCurveInt P).apOfModel 3 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 4 ∣ ((freyCurveInt P).reductionMod 3).card :=
    FreyCurve.four_dvd_card_reductionMod P (by decide) hgood
  have hpos : 0 < ((freyCurveInt P).reductionMod 3).card :=
    ((freyCurveInt P).reductionMod 3).card_pos
  have hle : ((freyCurveInt P).reductionMod 3).card ≤ 2 * Nat.card (ZMod 3) + 1 :=
    ((freyCurveInt P).reductionMod 3).card_le_two_mul_add_one
  rw [Nat.card_zmod] at hle

  have hcase : ((freyCurveInt P).reductionMod 3).card = 4 := by omega

  simp only [apOfModel, traceOfFrobenius, hcase, Nat.card_zmod]
  norm_num
