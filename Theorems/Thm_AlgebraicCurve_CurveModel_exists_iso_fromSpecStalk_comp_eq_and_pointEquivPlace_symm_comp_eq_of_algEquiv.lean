import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {L : Type u} [Field L] [Algebra K L]
    (M : CurveModel K L) (V : L ≃ₐ[K] L) (hV : (V : L →ₐ[K] L).toRingHom.IsIntegral) :
    ∃ h : M.C ≅ M.C, h.hom ≫ M.toBase = M.toBase ∧
      M.C.fromSpecStalk (genericPoint M.C) ≫ h.hom =
        Spec.map (CommRingCat.ofHom
          (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      ∀ P : Place K L,
        (M.pointEquivPlace.symm P).1 ≫ h.hom = (M.pointEquivPlace.symm (P.restrictAlong (V : L →ₐ[K] L) hV)).1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv.solution
