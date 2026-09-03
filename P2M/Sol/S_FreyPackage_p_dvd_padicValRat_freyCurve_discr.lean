import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyPackage_freyCurveInt_map
import Theorems.Thm_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr
import P2M.Util
namespace P2MW.S_FreyPackage_p_dvd_padicValRat_freyCurve_discr

theorem RibetLayer.freyCurve_Δ_eq_cast (P : FreyPackage) : P.freyCurve.Δ = (P.freyCurveInt.Δ : ℚ) := by
  rw [← P.freyCurveInt_map, WeierstrassCurve.map_Δ]
  rfl

theorem solution (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : (P.p : ℤ) ∣ padicValRat ℓ P.freyCurve.Δ := by
  rw [RibetLayer.freyCurve_Δ_eq_cast, padicValRat.of_int]
  exact Int.natCast_dvd_natCast.mpr (P.p_dvd_padicValInt_freyCurveInt_discr hℓ hℓ2)
