import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    (p : ℕ) (hp : p ≠ 0) (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦi : Φ.toRingHom.IsIntegral) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p)
    (w : AlgebraicCurve.Place K L) :
    w.restrictAlong Φ hΦi = g • w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow.solution
