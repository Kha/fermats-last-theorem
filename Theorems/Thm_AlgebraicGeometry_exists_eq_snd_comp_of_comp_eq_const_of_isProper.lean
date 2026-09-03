import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX] [IsIntegral X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) (hY : ConnectedSpace Y)
    (fZ : Z ⟶ Spec (CommRingCat.of k)) [IsSeparated fZ]
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ fY = 𝟙 _)
    (φ : pullback fX fY ⟶ Z) (hφ : φ ≫ fZ = pullback.fst fX fY ≫ fX)
    (z₀ : Spec (CommRingCat.of k) ⟶ Z)
    (hconst : pullback.lift (𝟙 X) (fX ≫ y₀) (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id]) ≫ φ = fX ≫ z₀) :
    φ = pullback.snd fX fY ≫ (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp]) ≫ φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.solution
