import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isPullback_action_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} [Nonempty N] (i : N ⟶ G) [IsClosedImmersion i] (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q) (hq : q ≫ fQ = f)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q] [QuasiCompact q]
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q) :
    SmoothOfRelativeDimension h q ∧ SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by

  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange h
  haveI h1 : SmoothOfRelativeDimension h (pullback.snd (i ≫ f) f) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension h) _ _ inferInstance

  have hq' : SmoothOfRelativeDimension h q :=
    AlgebraicGeometry.SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective h hR

  haveI : Nonempty G := Nonempty.map i.base inferInstance
  haveI : SmoothOfRelativeDimension g (q ≫ fQ) := by rw [hq]; infer_instance
  haveI := hq'
  obtain ⟨hQ, hle⟩ := AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field fQ q g h
  exact ⟨hq', hQ, hle⟩

#print axioms solution
