import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    {K : Type u} [Field K] [IsAlgClosed K]
    {L : Type u} [Field L] [Algebra K L] {L' : Type u} [Field L'] [Algebra K L']
    (M : CurveModel K L) (M' : CurveModel K L')
    (φ : L' →ₐ[K] L) (hφ : φ.toRingHom.IsIntegral)
    (πM : M.C ⟶ M'.C) (hπM : πM ≫ M'.toBase = M.toBase)
    (hgen : M.C.fromSpecStalk (genericPoint M.C) ≫ πM =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M'.ffEquiv.symm.toRingHom))) ≫
        M'.C.fromSpecStalk (genericPoint M'.C))
    (y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (V : M.C.Opens) (hyV : y.1.base (IsLocalRing.closedPoint K) ∈ V)
    (hV : FormallyUnramified (V.ι ≫ πM)) :
    Place.ramificationIndexAlong φ (M.pointEquivPlace y) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified.solution
