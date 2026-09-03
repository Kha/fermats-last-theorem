import Mathlib
import P2M.Util
namespace P2MW.S_Subalgebra_fg_restrictScalars_and_le_of_fg

set_option autoImplicit false

universe u

theorem solution
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (T : Subalgebra A₀ A) (hT : T.FG) (T' : Subalgebra ↥T A) (hT' : T'.FG) :
    (T'.restrictScalars A₀).FG ∧ (T : Set A) ⊆ (T'.restrictScalars A₀ : Set A) := by
  classical
  obtain ⟨s, rfl⟩ := hT
  obtain ⟨t, rfl⟩ := hT'
  have key : (Algebra.adjoin (↥(Algebra.adjoin A₀ (↑s : Set A))) (↑t : Set A)).restrictScalars A₀ =
      Algebra.adjoin A₀ ((↑s : Set A) ∪ ↑t) :=
    (Algebra.adjoin_union_eq_adjoin_adjoin A₀ (↑s : Set A) ↑t).symm
  refine ⟨⟨s ∪ t, ?_⟩, ?_⟩
  · rw [key, Finset.coe_union]
  · rw [key]
    exact Algebra.adjoin_mono Set.subset_union_left
