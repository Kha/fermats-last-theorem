import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (𝔐 : AlgebraicCurve.CurveModel K L)
    {X B : Scheme.{u}} (πX : X ⟶ B) (s : Spec (CommRingCat.of K) ⟶ B)
    (e : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX s) (he : IsIso e)
    (he_snd : e ≫ CategoryTheory.Limits.pullback.snd πX s = 𝔐.toBase)
    (P Q : Place K L)
    (h : (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s =
      (𝔐.pointEquivPlace.symm Q).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s) :
    P = Q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq.solution
