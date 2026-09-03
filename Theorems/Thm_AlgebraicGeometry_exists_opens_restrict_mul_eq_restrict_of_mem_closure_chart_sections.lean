import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    {A : Type u} [CommRing A] (φ : R →+* A)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom φ))))
    (hz : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base z ∈ ι ''ᵁ ⊤)
    (U : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens) (hzU : z ∈ U)
    (s : Γ(pullback f (Spec.map (CommRingCat.ofHom φ)), U)) :
    ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens) (_ : z ∈ W) (hWU : W ≤ U)
      (hWV : W ≤ (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤))
      (σ τ : Γ(pullback f (Spec.map (CommRingCat.ofHom φ)), (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤))),
      σ ∈ Subring.closure
          (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app (ι ''ᵁ ⊤)).hom
              ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
           Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
              (homOfLE (le_top : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ ⊤)).op).hom
              ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∧
      τ ∈ Subring.closure
          (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app (ι ''ᵁ ⊤)).hom
              ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
           Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
              (homOfLE (le_top : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ ⊤)).op).hom
              ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∧
      IsUnit (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom τ) ∧
      ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWU).op).hom s *
          ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom τ =
        ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections.solution
