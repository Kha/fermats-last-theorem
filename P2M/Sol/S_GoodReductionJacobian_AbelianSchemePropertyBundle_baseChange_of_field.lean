import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) {k : Type u} [Field k]
    (ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    AbelianSchemePropertyBundle k (pullback.snd f ι) := by
  refine ⟨MorphismProperty.pullback_snd (P := @Smooth) f ι hA.smooth,
    MorphismProperty.pullback_snd (P := @IsProper) f ι hA.proper, fun s => ?_,
    hA.hasGroupLaw.map fun G => G.baseChange ι⟩
  have hGI : GeometricallyIntegral f :=
    (GeometricallyIntegral.iff_geometricallyIntegral_fiber f).2 fun s =>
      (abelianSchemePropertyBundle_fibreStr hA s).geometricallyIntegral
  have hInt : IsIntegral (pullback f ι) :=
    pullback_of_geometrically hGI.geometrically_isIntegral k ι
  have huniv : (pullback.snd f ι).base ⁻¹' {s} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [huniv]
  exact (IrreducibleSpace.isIrreducible_univ _).isConnected
