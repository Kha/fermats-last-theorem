import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion
    (W : Scheme.{u}) {ι : Type u} [Nonempty ι] (U : ι → Scheme.{u}) (f : ∀ i, W ⟶ U i)
    [∀ i, IsOpenImmersion (f i)] :
    ∃ (Y : Scheme.{u}) (g : ∀ i, U i ⟶ Y),
      (∀ i, IsOpenImmersion (g i)) ∧
      (∀ i j, f i ≫ g i = f j ≫ g j) ∧
      (⋃ i, Set.range (g i).base = Set.univ) ∧
      (∀ i j, i ≠ j → Set.range (g i).base ∩ Set.range (g j).base = Set.range (f i ≫ g i).base) ∧
      (∀ (Z : Scheme.{u}) (h : ∀ i, U i ⟶ Z), (∀ i j, f i ≫ h i = f j ≫ h j) →
        ∃! k : Y ⟶ Z, ∀ i, g i ≫ k = h i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion.solution
