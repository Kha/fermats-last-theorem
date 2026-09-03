import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.map_transEquiv_eq_transEquiv_map_of_algHom
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] [IsAlgClosed K'] (W : WeierstrassCurve F) [W.IsElliptic] (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    (S : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    Φ (transEquiv W K S h) = transEquiv W K' (WeierstrassCurve.Affine.Point.map f S) (Φ h) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.solution
