import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (s s' : T ⟶ X) (h : s ≫ f = s' ≫ f) (t₀ : ↥T) (ht₀ : ∀ t : ↥T, t ⤳ t₀)
    (hΔ : (pullback.lift s s' h).base t₀ ∈ Set.range (pullback.diagonal f).base) :
    s = s' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal.solution
