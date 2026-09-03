import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback
    {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    {X X₁ : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase) :
    ∃ ρ : pullback toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
        pullback f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))),
      ρ.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) =
        pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
          e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback.solution
