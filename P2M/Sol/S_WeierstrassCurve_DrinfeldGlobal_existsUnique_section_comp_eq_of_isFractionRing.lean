import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_section_comp_eq_of_isFractionRing

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀)
    (s : Spec (CommRingCat.of K) ⟶ projModelCR W₀)
    (hs : s ≫ projModelStrCR W₀ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K))) :
    ∃! P₀ : Section W₀, Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) ≫ P₀.1 = s := by

  haveI : IsProper (projModelStrCR W₀) := WeierstrassProjModel.projModelStrCR_isProper W₀
  have hVC : ValuativeCriterion (projModelStrCR W₀) := by
    have h : IsProper (projModelStrCR W₀) := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let S : ValuativeCommSq (projModelStrCR W₀) :=
    { R := R₀, K := K, i₁ := s, i₂ := 𝟙 _, commSq := ⟨by rw [Category.comp_id]; exact hs⟩ }
  obtain ⟨hU⟩ := hVC S
  let l := (default : S.commSq.LiftStruct)
  refine ⟨⟨l.l, by simpa using l.fac_right⟩, l.fac_left, ?_⟩
  intro P hP
  have : (⟨P.1, hP, by simpa using P.2⟩ : S.commSq.LiftStruct) = l := Subsingleton.elim _ _
  apply Subtype.ext
  exact congrArg CommSq.LiftStruct.l this
