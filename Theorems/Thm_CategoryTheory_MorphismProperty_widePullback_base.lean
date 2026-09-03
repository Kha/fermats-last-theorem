import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import P2M.Util
import P2M.Sol.S_CategoryTheory_MorphismProperty_widePullback_base

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

theorem CategoryTheory.MorphismProperty.widePullback_base
    {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
    {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S) (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_MorphismProperty_widePullback_base.solution
