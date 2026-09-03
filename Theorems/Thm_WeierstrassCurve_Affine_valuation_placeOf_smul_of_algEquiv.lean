import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.valuation_placeOf_smul_of_algEquiv {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] (W : WeierstrassCurve F) (σ : K ≃ₐ[F] K) (Φ : (W⁄K).FunctionField →+* (W⁄K).FunctionField) (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) = algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K))))) [IsDedekindDomain (W⁄K).CoordinateRing] {P : (W⁄K).Point} (hP : P ≠ 0) (hσP : σ • P ≠ 0) (f : (W⁄K).FunctionField) : (placeOf W K (σ • P) hσP).valuation (W⁄K).FunctionField (Φ f) = (placeOf W K P hP).valuation (W⁄K).FunctionField f := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv.solution
