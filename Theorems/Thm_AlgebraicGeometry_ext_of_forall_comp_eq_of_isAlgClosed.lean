import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of κ)) (fY : Y ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType fX] [IsReduced X] [IsSeparated fY]
    {f g : X ⟶ Y} (hf : f ≫ fY = fX) (hg : g ≫ fY = fX)
    (h : ∀ x : Spec (CommRingCat.of κ) ⟶ X, x ≫ fX = 𝟙 _ → x ≫ f = x ≫ g) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed.solution
