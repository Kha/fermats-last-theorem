import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_exists_ringHom_functionField_baseChange_of_algHom

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.exists_ringHom_functionField_baseChange_of_algHom
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K']
    (W : WeierstrassCurve F) (f : K →ₐ[F] K') :
    ∃ Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField,
      ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
        algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField
          (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_exists_ringHom_functionField_baseChange_of_algHom.solution
