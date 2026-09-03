import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

theorem AlgebraicGeometry.exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective
    {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
    (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    ∃ h : B ⟶ C, IsMonHom h ∧ f ≫ h = g ∧ ∀ h' : B ⟶ C, f ≫ h' = g → h' = h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective.solution
