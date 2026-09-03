import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow

set_option autoImplicit false

theorem AlgebraicCurve.RationalFunctionField.finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
    (K : Type*) [Field K] [IsAlgClosed K] (q : ℕ) (hq : 1 < q) (hqK : (q : K) = 0)
    (φ : RatFunc K →ₐ[K] RatFunc K) (hφi : φ.toRingHom.IsIntegral)
    (hφ : φ RatFunc.X = RatFunc.X ^ q) :
    (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)).Finite ∧
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)) = q + 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow.solution
