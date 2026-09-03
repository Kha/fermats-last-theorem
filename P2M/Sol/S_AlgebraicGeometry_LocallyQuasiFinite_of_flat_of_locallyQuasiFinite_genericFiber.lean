import Mathlib
import Theorems.Thm_Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [Flat f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    LocallyQuasiFinite f := by
  suffices main : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)), Flat f → LocallyOfFiniteType f →
      LocallyQuasiFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) →
      LocallyQuasiFinite f by
    exact main f ‹_› ‹_› ‹_›
  clear! Y
  intro Y f hf hft hgen
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyQuasiFinite) Y.affineCover).mpr
      fun i => this _ inferInstance inferInstance ?_ ⟨_, rfl⟩
    rw [← pullbackRightPullbackFstIso_inv_snd_snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Y.affineCover.f i)]
    infer_instance
  obtain ⟨S, rfl⟩ := hY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hf
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]
  algebraize [φ.hom]

  have hgen' : LocallyQuasiFinite (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := hgen
  rw [← pullbackSpecIso_hom_snd R S K,
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyQuasiFinite),
    HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite), CommRingCat.hom_ofHom] at hgen'
  have h2 := (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective
    (Algebra.TensorProduct.comm R S K).toRingEquiv.toRingHom
    (Algebra.TensorProduct.comm R S K).surjective)).comp hgen'
  have h3 : (Algebra.TensorProduct.comm R S K).toRingEquiv.toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := R) (A := S) (B := K) : K →ₐ[R] _) : K →+* _) =
      algebraMap K (TensorProduct R K S) :=
    RingHom.ext fun k => by simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h3, RingHom.quasiFinite_algebraMap] at h2
  show (algebraMap R S).QuasiFinite
  rw [RingHom.quasiFinite_algebraMap]
  exact Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber (K := K) h2
