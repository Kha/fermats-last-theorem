import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_appLE_apply_eq_of_comp_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.Scheme.Hom.exists_appLE_apply_eq_of_comp_eq_id
    {B B' : Type u} [CommRing B] [CommRing B']
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of B)) (gX : X ⟶ Spec (CommRingCat.of B'))
    (φ : X ⟶ Y) (k : Y ⟶ X) (hk : k ≫ φ = 𝟙 Y)
    (p : B' →+* B) (hkp : k ≫ gX = gY ≫ Spec.map (CommRingCat.ofHom p))
    (U : Y.Opens) :
    ∃ hle : U ≤ k ⁻¹ᵁ (φ ⁻¹ᵁ U),
      (∀ m : Γ(Y, U), (k.appLE (φ ⁻¹ᵁ U) U hle).hom ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom m) = m) ∧
      (letI := algebraOfHom gY U
       letI := algebraOfHom gX (φ ⁻¹ᵁ U)
       ∀ x : B', (k.appLE (φ ⁻¹ᵁ U) U hle).hom (algebraMap B' Γ(X, φ ⁻¹ᵁ U) x) = algebraMap B Γ(Y, U) (p x)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_appLE_apply_eq_of_comp_eq_id.solution
