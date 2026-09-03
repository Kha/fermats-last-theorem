import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_thetaL_laurentMap_lambdaDworkQuotient
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.thetaL_laurentMap_lambdaDworkQuotient
    (q : ℕ) [Fact q.Prime]
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q lambdaInt - lambdaInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    thetaL k (laurentMap (Int.castRingHom k) S) =
      thetaL k (lambdaModC k) ^ q - lambdaModC k ^ (q - 1) * thetaL k (lambdaModC k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_thetaL_laurentMap_lambdaDworkQuotient.solution
