import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import P2M.Util
import P2M.Sol.S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory

theorem CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {M N M' N' : C} (e : M ≅ M') (h : Nonempty (M ⊗ N ≅ 𝟙_ C)) (h' : Nonempty (M' ⊗ N' ≅ 𝟙_ C)) :
    Nonempty (N ≅ N') := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit.solution
