import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_eq_pullback_snd_comp_of_isProper
    {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K))
    (z : Z ⟶ Spec (CommRingCat.of K))
    [IsProper x] [IsIntegral X] [IsIntegral Y] [IsSeparated z]
    [LocallyOfFiniteType y] [LocallyOfFiniteType z] [IsReduced (pullback x y)]
    (f : pullback x y ⟶ Z) (hf : f ≫ z = pullback.fst x y ≫ x)
    (y₀ : Spec (CommRingCat.of K) ⟶ Y) (hy₀ : y₀ ≫ y = 𝟙 _)
    (z₀ : Spec (CommRingCat.of K) ⟶ Z)
    (h : pullback.lift (𝟙 X) (x ≫ y₀) (by rw [Category.id_comp, Category.assoc, hy₀,
      Category.comp_id]) ≫ f = x ≫ z₀) :
    ∃ g : Y ⟶ Z, f = pullback.snd x y ≫ g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper.solution
