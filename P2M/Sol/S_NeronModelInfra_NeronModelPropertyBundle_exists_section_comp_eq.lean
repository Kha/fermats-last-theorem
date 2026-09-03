import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
namespace P2MW.S_NeronModelInfra_NeronModelPropertyBundle_exists_section_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem solution
    {R K : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (h : NeronModelPropertyBundle R K f)
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1 = x := by
  have hιdef : specGenericFibreInclusion R K = Spec.map (CommRingCat.ofHom (algebraMap R K)) := rfl
  rw [← hιdef] at hx ⊢

  have hx' : (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K) ≫ x) ≫ f =
      pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K := by
    rw [Category.assoc, hx]
  let ψ : SchemeHomOver (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)) :=
    ⟨pullback.lift (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K) ≫ x)
        (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K)) hx',
      pullback.lift_snd _ _ _⟩

  obtain ⟨s, hs⟩ := (h.neronMapping (Spec (CommRingCat.of R)) (𝟙 _) inferInstance).2 ψ
  refine ⟨s, ?_⟩

  have h1 := congrArg (fun φ => φ.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) hs
  rw [genericFibreRestrict_coe_comp_fst] at h1
  change pullback.fst (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K) ≫ s.1 =
    pullback.lift (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K) ≫ x) _ hx' ≫
      pullback.fst f (specGenericFibreInclusion R K) at h1
  rw [pullback.lift_fst] at h1

  have hc : pullback.fst (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K) =
      pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K := by
    have := pullback.condition (f := 𝟙 (Spec (CommRingCat.of R))) (g := specGenericFibreInclusion R K)
    rw [Category.comp_id] at this
    exact this
  rw [hc, Category.assoc] at h1
  exact (cancel_epi (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (specGenericFibreInclusion R K))).mp h1
