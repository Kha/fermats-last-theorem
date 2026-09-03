import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve

open WeierstrassCurve
theorem FreyPackage.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve (P : FreyPackage) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf P.freyCurve) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓabc : (ℓ : ℤ) ∣ P.a * P.b * P.c) : ¬ W.IsGoodPrimeFor ℓ := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve.solution
