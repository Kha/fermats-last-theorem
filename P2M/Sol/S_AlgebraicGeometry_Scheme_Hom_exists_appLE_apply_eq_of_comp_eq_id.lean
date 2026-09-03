import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_appLE_apply_eq_of_comp_eq_id

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    {B B' : Type u} [CommRing B] [CommRing B']
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of B)) (gX : X ⟶ Spec (CommRingCat.of B'))
    (φ : X ⟶ Y) (k : Y ⟶ X) (hk : k ≫ φ = 𝟙 Y)
    (p : B' →+* B) (hkp : k ≫ gX = gY ≫ Spec.map (CommRingCat.ofHom p))
    (U : Y.Opens) :
    ∃ hle : U ≤ k ⁻¹ᵁ (φ ⁻¹ᵁ U),
      (∀ m : Γ(Y, U), (k.appLE (φ ⁻¹ᵁ U) U hle).hom ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom m) = m) ∧
      (letI := algebraOfHom gY U
       letI := algebraOfHom gX (φ ⁻¹ᵁ U)
       ∀ x : B', (k.appLE (φ ⁻¹ᵁ U) U hle).hom (algebraMap B' Γ(X, φ ⁻¹ᵁ U) x) = algebraMap B Γ(Y, U) (p x)) := by
  classical
  have hpre : k ⁻¹ᵁ (φ ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, hk]; rfl
  refine ⟨hpre.ge, ?_, ?_⟩
  · intro m
    have hc : φ.appLE U (φ ⁻¹ᵁ U) le_rfl ≫ k.appLE (φ ⁻¹ᵁ U) U hpre.ge = 𝟙 _ := by
      rw [Scheme.Hom.appLE_comp_appLE]
      have gen : ∀ (ψ : Y ⟶ Y), ψ = 𝟙 Y → ∀ (h : U ≤ ψ ⁻¹ᵁ U), ψ.appLE U U h = 𝟙 _ := by
        rintro ψ rfl h
        simp only [Scheme.Hom.appLE]
        rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _]
        erw [Y.presheaf.map_id]
        exact Category.id_comp _
      exact gen _ hk _
    have := congrArg (fun f => f.hom m) hc
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply] using this
  · letI := algebraOfHom gY U
    letI := algebraOfHom gX (φ ⁻¹ᵁ U)
    intro x
    rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    have gen : ∀ (ψ : Y ⟶ Spec (CommRingCat.of B')), ψ = gY ≫ Spec.map (CommRingCat.ofHom p) → ∀ (h : U ≤ ψ ⁻¹ᵁ ⊤),
        (ψ.appLE ⊤ U h).hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv x) =
          (gY.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (p x)) := by
      rintro ψ rfl h
      rw [← Scheme.Hom.appLE_comp_appLE gY (Spec.map (CommRingCat.ofHom p)) ⊤ ((Spec.map (CommRingCat.ofHom p)) ⁻¹ᵁ ⊤) U
        le_rfl le_top, ← Scheme.Hom.app_eq_appLE, CommRingCat.comp_apply]
      congr 1
      have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom p)
      have := congrArg (fun f => f.hom x) nat
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
      exact this.symm
    exact gen _ hkp _
