module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Sol.S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable
import P2M.Sol.S_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional
import P2M.Sol.S_AlgebraicCurve_instIsCurveOverRatFunc
import P2M.Sol.S_AlgebraicCurve_kaehlerRankOne_of_transcendental
import P2M.Util
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

namespace P2MW.S_AlgebraicCurve_isCurveOver_of_transcendental

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IntermediateField

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F := by
  have hprin : HasPrincipalDivisors K F :=
    AlgebraicCurve.hasPrincipalDivisors_of_transcendental_of_isSeparable htr hfd hsep
  have hkae : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=
    AlgebraicCurve.kaehlerRankOne_of_transcendental htr hsep
  have hfin : ∀ v : Place K F, Module.Finite K v.ResidueField := by
    haveI := hfd
    haveI := hsep
    set e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr with he
    letI : Algebra (RatFunc K) F :=
      ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
    have hsq : RingHom.comp (algebraMap (RatFunc K) F)
          (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
        = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
      refine RingHom.ext fun a => ?_
      show algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
      rw [e.apply_symm_apply]
    haveI : IsScalarTower K (RatFunc K) F :=
      IsScalarTower.of_algebraMap_eq fun a => by
        show algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
        rw [e.commutes, ← IsScalarTower.algebraMap_apply]
    haveI : FiniteDimensional (RatFunc K) F :=
      Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
    haveI : Algebra.IsSeparable (RatFunc K) F :=
      Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
    intro v
    haveI h1 : Module.Finite (v.restrict (RatFunc K)).ResidueField v.ResidueField :=
      Place.finite_residueField_of_finiteDimensional (F := RatFunc K) v
    haveI h2 : Module.Finite K (v.restrict (RatFunc K)).ResidueField :=
      (AlgebraicCurve.instIsCurveOverRatFunc K).finiteResidue _
    exact Module.Finite.trans (v.restrict (RatFunc K)).ResidueField v.ResidueField
  exact { toHasPrincipalDivisors := hprin, finiteResidue := hfin, kaehler_free_rank_one := hkae }
end S_AlgebraicCurve_isCurveOver_of_transcendental
end P2MW

public section
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
open AlgebraicCurve IntermediateField
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem AlgebraicCurve.isCurveOver_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isCurveOver_of_transcendental.solution
end
