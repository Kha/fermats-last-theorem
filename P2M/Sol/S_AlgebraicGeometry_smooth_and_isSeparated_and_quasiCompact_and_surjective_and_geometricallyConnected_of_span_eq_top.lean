import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PropLoc

scoped instance isZariskiLocalAtTarget_geometricallyConnected :
    IsZariskiLocalAtTarget @GeometricallyConnected :=
  GeometricallyConnected.eq_geometrically ▸ inferInstance

theorem of_span_eq_top (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i : ι,
      P (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i))))))) :
    P g :=
  IsZariskiLocalAtTarget.of_openCover
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) f hf).openCover
    fun i => h i

end PropLoc
p2m_reactivate "P2MW.S_AlgebraicGeometry_smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top.PropLoc"

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i : ι,
      Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      IsSeparated (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      QuasiCompact (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      Surjective (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      GeometricallyConnected (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i))))))) :
    Smooth g ∧ IsSeparated g ∧ QuasiCompact g ∧ Surjective g ∧ GeometricallyConnected g :=
  ⟨PropLoc.of_span_eq_top @Smooth g f hf fun i => (h i).1,
    PropLoc.of_span_eq_top @IsSeparated g f hf fun i => (h i).2.1,
    PropLoc.of_span_eq_top @QuasiCompact g f hf fun i => (h i).2.2.1,
    PropLoc.of_span_eq_top @Surjective g f hf fun i => (h i).2.2.2.1,
    PropLoc.of_span_eq_top @GeometricallyConnected g f hf fun i => (h i).2.2.2.2⟩
