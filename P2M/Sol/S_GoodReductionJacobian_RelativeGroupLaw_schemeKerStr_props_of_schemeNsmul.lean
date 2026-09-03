import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_schemeKerStr_props_of_schemeNsmul

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct

theorem solution
    {R : Type u} [CommRing R] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R g) (n : ℕ)
    (hqf : LocallyQuasiFinite (L.schemeNsmul n)) (hfl : Flat (L.schemeNsmul n)) :
    LocallyQuasiFinite (L.schemeKerStr n) ∧ QuasiCompact (L.schemeKerStr n) ∧ Flat (L.schemeKerStr n) ∧
      IsSeparated (L.schemeKerStr n) ∧
      IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ∧
      IsClosedImmersion (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧
      (Smooth g → LocallyOfFiniteType g) := by
  haveI := hqf
  haveI := hfl

  have hover : L.schemeNsmul n ≫ g = g := L.schemeNsmul_over n

  haveI : QuasiCompact (L.schemeNsmul n) :=
    MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) (L.schemeNsmul n) g
      inferInstance (by rw [hover]; infer_instance)
  haveI : IsSeparated (L.schemeNsmul n) :=
    MorphismProperty.of_postcomp (W := @IsSeparated) (W' := ⊤) (L.schemeNsmul n) g trivial
      (by rw [hover]; infer_instance)

  have hone : IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated)
      (L.one (𝟙 (Spec (CommRingCat.of R)))).1 g inferInstance
      (by rw [(L.one (𝟙 (Spec (CommRingCat.of R)))).2]; infer_instance)
  haveI := hone
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hone, inferInstance, fun _ => inferInstance⟩
