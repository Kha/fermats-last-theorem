import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_pullback_map_eq_pullback_map_of_isSeparated
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
    (g₁ g₂ : X ⟶ Y) (h₁ : g₁ ≫ fY = fX) (h₂ : g₂ ≫ fY = fX)
    (H : pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₁ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₁]) (by rw [Category.comp_id, Category.id_comp]) =
         pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₂ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₂]) (by rw [Category.comp_id, Category.id_comp])) :
    g₁ = g₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated.solution
