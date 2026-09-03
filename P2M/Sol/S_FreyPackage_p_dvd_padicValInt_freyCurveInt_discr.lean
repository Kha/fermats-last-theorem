import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyPackage_padicValInt_freyCurveInt_discr
import P2M.Util
namespace P2MW.S_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr

theorem solution (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : P.p ∣ padicValInt ℓ P.freyCurveInt.Δ :=
  ⟨2 * padicValInt ℓ (P.a * P.b * P.c), by rw [P.padicValInt_freyCurveInt_discr hℓ hℓ2]; ring⟩
