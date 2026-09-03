import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
import Theorems.Thm_AlgebraicGeometry_flat_stalkQuotient_of_forall_flat_schemeFibreEndo
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_fibrewiseFlat
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits NeronModelInfra GoodReductionJacobian

set_option maxHeartbeats 6400000 in
theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f) (n : ℕ) (hn : 0 < n)
    (hfib : ∀ s, Flat (schemeFibreEndo f (L.schemeNsmul n) (L.schemeNsmul_over n) s)) :
    Flat (L.schemeNsmul n) := by
  haveI : Smooth f := hJ.smooth
  haveI : IsProper f := hJ.proper
  haveI : IsSeparated f := inferInstance
  haveI : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : Flat (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over n]; infer_instance
  refine Flat.of_stalkMap (L.schemeNsmul n) (fun x => ?_)
  letI := (f.stalkMap ((L.schemeNsmul n).base x)).hom.toAlgebra
  letI := ((L.schemeNsmul n).stalkMap x).hom.toAlgebra
  letI := (((L.schemeNsmul n).stalkMap x).hom.comp
    (f.stalkMap ((L.schemeNsmul n).base x)).hom).toAlgebra
  haveI : IsScalarTower ((Spec (CommRingCat.of R)).presheaf.stalk
        (f.base ((L.schemeNsmul n).base x)))
      (J.presheaf.stalk ((L.schemeNsmul n).base x)) (J.presheaf.stalk x) :=
    .of_algebraMap_eq' rfl
  haveI : IsLocalHom (algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk
      (f.base ((L.schemeNsmul n).base x))) (J.presheaf.stalk ((L.schemeNsmul n).base x))) :=
    inferInstanceAs (IsLocalHom (f.stalkMap ((L.schemeNsmul n).base x)).hom)
  haveI : IsLocalHom (algebraMap (J.presheaf.stalk ((L.schemeNsmul n).base x))
      (J.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom ((L.schemeNsmul n).stalkMap x).hom)
  letI := Ideal.Quotient.algebraQuotientOfLEComap
    (p := (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk
      (f.base ((L.schemeNsmul n).base x)))).map
      (f.stalkMap ((L.schemeNsmul n).base x)).hom)
    (P := (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk
      (f.base ((L.schemeNsmul n).base x)))).map
      (((L.schemeNsmul n).stalkMap x).hom.comp (f.stalkMap ((L.schemeNsmul n).base x)).hom))
    (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]; exact le_rfl)
  have heq : ((L.schemeNsmul n).stalkMap x).hom.comp
        (f.stalkMap ((L.schemeNsmul n).base x)).hom
      = ((L.schemeNsmul n ≫ f).stalkMap x).hom := by rw [Scheme.Hom.stalkMap_comp]; rfl
  have hflat : (((L.schemeNsmul n).stalkMap x).hom.comp
      (f.stalkMap ((L.schemeNsmul n).base x)).hom).Flat :=
    heq ▸ Flat.stalkMap (L.schemeNsmul n ≫ f) x
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
      (RingHom.flat_algebraMap_iff.mp hflat)
      (AlgebraicGeometry.flat_stalkQuotient_of_forall_flat_schemeFibreEndo
        f (L.schemeNsmul n) (L.schemeNsmul_over n) x hfib))
