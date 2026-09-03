import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
set_option autoImplicit false
open ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
    (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (f y : modularFunctionFieldFullC K N) (hy : frobeniusModL K N ℓ y = f ^ ℓ) (n : ℤ) :
    (qExpansionDiffAlong (modularFunctionFieldFullC K N).val
        (y⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) y)).coeff n =
      ((qExpansionDiffAlong (modularFunctionFieldFullC K N).val
        (f⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) f)).coeff n) ^ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow.solution
