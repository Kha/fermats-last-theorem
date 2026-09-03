import Mathlib
import Definitions.Def_AlgebraicGeometry_SubalgebraStages
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.SubalgebraStages.nonempty_isLimit_cone
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ι →o Subalgebra A₀ A) (hS : ∀ a : A, ∃ i, a ∈ S i)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) :
    Nonempty (IsLimit (SubalgebraStages.cone S f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.solution
