import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import P2M.Util
namespace P2MW.S_ModularCurve_frobenius_identity_lambda

set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    lambdaNModC K ℓ = (lambdaModC K) ^ ℓ := by
  rw [lambdaNModC, lambdaModC, pow_char_eq_map_frobenius_qExpand ℓ]
  change _ = laurentMap (frobenius K ℓ) (qExpand K ℓ (laurentMap (Int.castRingHom K) lambdaInt))
  rw [laurentMap_qExpand, laurentMap_laurentMap]
  have hcomp : (frobenius K ℓ).comp (Int.castRingHom K) = Int.castRingHom K := RingHom.ext_int _ _
  rw [hcomp]
