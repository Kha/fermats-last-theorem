import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback
    {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    {X X₁ : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase)
    (x : X) (hx : toBase.base x = IsLocalRing.closedPoint A)
    (r : X₁.presheaf.stalk ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x))
    (hr : ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap x).hom r ∈
      Ideal.map ((X.presheaf.germ ⊤ x trivial).hom.comp
        (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
        (IsLocalRing.maximalIdeal A)) :
    r ∈ Ideal.map ((X₁.presheaf.germ ⊤ ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)
        trivial).hom.comp (f₁.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom))
      (IsLocalRing.maximalIdeal A₁) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback.solution
