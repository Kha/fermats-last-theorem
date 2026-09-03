import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isUnit_mul_eq_mem_closure_of_stalk_pullback
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

theorem AlgebraicGeometry.exists_isUnit_mul_eq_mem_closure_of_stalk_pullback
    {R A O : Type u} [CommRing R] [CommRing A] [CommRing O] [Algebra R A] [Algebra R O]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (i : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion i]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R O)))))
    (hx : x ∈ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ (i ''ᵁ ⊤))
    (s : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.stalk x) :
    ∃ u w : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.stalk x,
      IsUnit w ∧ s * w = u ∧
      u ∈ Subring.closure
        (Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.germ
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ (i ''ᵁ ⊤)) x hx).hom
            (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).app (i ''ᵁ ⊤)).hom
              ((i.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∪
         Set.range (fun o : O => ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.germ ⊤ x trivial).hom
            (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))) ∧
      w ∈ Subring.closure
        (Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.germ
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ (i ''ᵁ ⊤)) x hx).hom
            (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).app (i ''ᵁ ⊤)).hom
              ((i.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∪
         Set.range (fun o : O => ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.germ ⊤ x trivial).hom
            (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isUnit_mul_eq_mem_closure_of_stalk_pullback.solution
