import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import P2M.Util
import P2M.Sol.S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory

theorem CategoryTheory.MonoidalClosed.isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    {M N : C} (e : M ⊗ N ≅ 𝟙_ C) :
    (∀ X : C, IsIso ((ihom.ev M).app X)) ∧
      IsIso (MonoidalClosed.curry
        ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))) := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit.solution
