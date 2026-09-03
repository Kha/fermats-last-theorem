import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_exists_baseChange_eq_of_forall_smul_eq

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.exists_baseChange_eq_of_forall_smul_eq {R : Type*} {S : Type*} {K : Type*} [CommRing R] [Field S] [Field K] [DecidableEq S] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] [IsGalois S K] (W' : Affine R) (x : (W'⁄K).Point) (hx : ∀ σ : K ≃ₐ[S] K, σ • x = x) : ∃ y : (W'⁄S).Point, Point.baseChange S K y = x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_exists_baseChange_eq_of_forall_smul_eq.solution
