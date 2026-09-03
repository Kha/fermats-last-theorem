import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_fibrePower_represents_tuples

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_fibrePower_represents_tuples
    {B Y : Scheme.{u}} (πY : Y ⟶ B) (n : ℕ) :
    ∃ (P : Scheme.{u}) (πP : P ⟶ B) (q : Fin n → (P ⟶ Y)),
      (∀ l, q l ≫ πY = πP) ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ B) (g : Fin n → (T ⟶ Y)), (∀ l, g l ≫ πY = t) →
        ∃! G : T ⟶ P, G ≫ πP = t ∧ ∀ l, G ≫ q l = g l) ∧
      (IsSeparated πY → IsSeparated πP) ∧
      (LocallyOfFiniteType πY → LocallyOfFiniteType πP) ∧
      (LocallyOfFinitePresentation πY → LocallyOfFinitePresentation πP) ∧
      (∀ U : Fin n → Y.Opens, (∀ l, IsClosed ((U l : Set Y))) → (∀ l, QuasiCompact ((U l).ι ≫ πY)) →
        IsClosed ((⨅ l, (q l) ⁻¹ᵁ (U l) : P.Opens) : Set P) ∧
        QuasiCompact ((⨅ l, (q l) ⁻¹ᵁ (U l)).ι ≫ πP)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_fibrePower_represents_tuples.solution
