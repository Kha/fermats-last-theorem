import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i : ι,
      Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      IsSeparated (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      QuasiCompact (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      Surjective (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      GeometricallyConnected (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i))))))) :
    Smooth g ∧ IsSeparated g ∧ QuasiCompact g ∧ Surjective g ∧ GeometricallyConnected g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top.solution
