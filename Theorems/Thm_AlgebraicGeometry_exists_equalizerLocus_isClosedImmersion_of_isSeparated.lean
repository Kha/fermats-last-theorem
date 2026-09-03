import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.exists_equalizerLocus_isClosedImmersion_of_isSeparated
    {B X Y : Scheme.{u}} (πX : X ⟶ B) (πY : Y ⟶ B) (hY : IsSeparated πY)
    {ι : Type v} [Fintype ι] (a b : ι → (X ⟶ Y))
    (ha : ∀ i, a i ≫ πY = πX) (hb : ∀ i, b i ≫ πY = πX) :
    ∃ (E : Scheme.{u}) (m : E ⟶ X), IsClosedImmersion m ∧
      (∀ i, m ≫ a i = m ≫ b i) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ X), (∀ i, g ≫ a i = g ≫ b i) → ∃! g' : T ⟶ E, g' ≫ m = g) ∧
      (LocallyOfFinitePresentation (pullback.diagonal πY) → LocallyOfFinitePresentation m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated.solution
