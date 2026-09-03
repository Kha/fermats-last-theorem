import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_hom_of_algHom
import P2M.Util
namespace P2MW.S_AlgebraicCurve_CurveModel_exists_hom_pointEquivPlace_restrict_eq
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

namespace HG1ACor

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

private theorem isIntegral_toAlgHom [Module.Finite F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral :=
  fun x => Algebra.IsIntegral.isIntegral (R := F) x

private theorem algebraAlong_toAlgHom :
    algebraAlong (IsScalarTower.toAlgHom K F F') = (inferInstance : Algebra F F') :=
  Algebra.algebra_ext _ _ fun _ => rfl

private theorem finiteAlong_toAlgHom [Module.Finite F F'] :
    FiniteAlong K (IsScalarTower.toAlgHom K F F') :=
  (congrArg (fun i : Algebra F F' => letI := i; Module.Finite F F') algebraAlong_toAlgHom).mpr
    ‹Module.Finite F F'›

private theorem finrankAlong_toAlgHom :
    finrankAlong K (IsScalarTower.toAlgHom K F F') = Module.finrank F F' :=
  congrArg (fun i : Algebra F F' => letI := i; Module.finrank F F') algebraAlong_toAlgHom

end HG1ACor

open HG1ACor in
open AlgebraicCurve.CurveModel in
theorem solution {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F']
    (M : CurveModel K F) (M' : CurveModel K F') :
    ∃ π : M'.C ⟶ M.C,
      π ≫ M.toBase = M'.toBase ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : M.C, π.finrank x = Module.finrank F F') ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M'.ffEquiv.toRingHom.comp ((algebraMap F F').comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      (∀ (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
          (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
        y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x) ∧
      ∀ π' : M'.C ⟶ M.C,
        M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
          M'.C.fromSpecStalk (genericPoint M'.C) ≫ π → π' = π := by
  obtain ⟨π, ha, hfinite, hflat, hlfp, hrank, hgen, hplace, huniq⟩ :=
    exists_hom_of_algHom M M' (IsScalarTower.toAlgHom K F F') isIntegral_toAlgHom
      finiteAlong_toAlgHom
  refine ⟨π, ha, hfinite, hflat, hlfp, fun x => ?_, hgen, fun y x hyx => ?_, huniq⟩
  · rw [hrank x, finrankAlong_toAlgHom]
  · obtain ⟨h, hpl⟩ := hplace (pointEquivClosedPoint M'.toBase y)
    have hx : pointEquivClosedPoint M.toBase x =
        ⟨π.base (pointEquivClosedPoint M'.toBase y).1, h⟩ := by
      apply Subtype.ext
      simp [← hyx]
    simp only [CurveModel.pointEquivPlace_apply]
    rw [hx, hpl]
    rfl

end
