import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    (act : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⟶ A)
    (hact : act ≫ f = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f)
    (V : A.Opens) (hV : IsAffineOpen V)
    (hle : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V ≤ act ⁻¹ᵁ V) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
        Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (ε : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
      (hε_fst : ∀ a : Γ(A, V),
        ε (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
      (hε_snd : ∀ h : H,
        ε (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h)
      (ρ : Γ(A, V) →ₐ[K] Γ(A, V) ⊗[K] H)
      (hρ : ∀ s : Γ(A, V), ρ s = ε ((act.appLE V ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) hle).hom s))
      (T : Type u) [CommRing T] [Algebra K T] (α : Γ(A, V) →ₐ[K] T) (χ : H →ₐ[K] T),
    hV.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Γ(A, V))) ∧
    ∃ hx : (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ hV.fromSpec) ≫ f =
        Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K H)),
      pullback.lift (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ hV.fromSpec) (Spec.map (CommRingCat.ofHom χ.toRingHom)) hx ≫ act =
        Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.lift α χ (fun _ _ => Commute.all _ _)).comp ρ).toRingHom) ≫
          hV.fromSpec := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart.solution
