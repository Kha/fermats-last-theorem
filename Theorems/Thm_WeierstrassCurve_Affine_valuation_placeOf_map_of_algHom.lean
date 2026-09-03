import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.valuation_placeOf_map_of_algHom
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] [IsDedekindDomain (W⁄K').CoordinateRing]
    (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    (h : (W⁄K).FunctionField) :
    (∀ (P : (W⁄K).Point) (hP : P ≠ 0) (hfP : WeierstrassCurve.Affine.Point.map f P ≠ 0),
        (placeOf W K' (WeierstrassCurve.Affine.Point.map f P) hfP).valuation (W⁄K').FunctionField (Φ h) =
          (placeOf W K P hP).valuation (W⁄K).FunctionField h) ∧
    (h ≠ 0 → ∀ (P' : (W⁄K').Point) (hP' : P' ≠ 0),
        (∀ P : (W⁄K).Point, WeierstrassCurve.Affine.Point.map f P ≠ P') →
        (placeOf W K' P' hP').valuation (W⁄K').FunctionField (Φ h) = 1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom.solution
