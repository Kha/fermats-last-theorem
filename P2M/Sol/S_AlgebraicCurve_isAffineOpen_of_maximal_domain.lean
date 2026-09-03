import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal
import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import P2M.Util
namespace P2MW.S_AlgebraicCurve_isAffineOpen_of_maximal_domain

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s)) :
    IsAffineOpen U := by

  let φ : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k[X]) :=
    (U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))

  haveI : IsProper φ := Scheme.Opens.isProper_toSpecPolynomial_of_maximal c
    (valuationRing_stalk_of_smoothOfRelativeDimension_one c) U s hU

  haveI : LocallyQuasiFinite φ := LocallyQuasiFinite.of_finite_preimage_singleton φ
    (Scheme.Opens.finite_preimage_singleton_toSpecPolynomial c U s hs)

  haveI : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  exact isAffine_of_isAffineHom φ
