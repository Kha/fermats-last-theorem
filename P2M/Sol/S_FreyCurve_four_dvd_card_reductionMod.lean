import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Mathlib.Algebra.Module.Torsion.Basic
import Theorems.Thm_FreyCurve_card_two_torsion_reductionMod
import P2M.Util
namespace P2MW.S_FreyCurve_four_dvd_card_reductionMod

open WeierstrassCurve FreyPackage

theorem solution (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    4 ∣ ((FreyPackage.freyCurveInt P).reductionMod q).card := by
  rw [← FreyCurve.card_two_torsion_reductionMod P hq2 hgood]
  exact AddSubgroup.card_dvd_of_injective
    (Submodule.torsionBy ℤ ((freyCurveInt P).reductionMod q).toAffine.Point 2).subtype.toAddMonoidHom
    (fun a b hab => Subtype.ext hab)
