import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    (X : Scheme.{0}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical

  have h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hU hxU using h

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨{ ι := Fin t.card
            U := fun i => U (t.equivFin.symm i).1
            isAffineOpen := fun i => hU _
            iSup_eq_top := ?_ }⟩
  refine top_le_iff.mp (fun x _ => ?_)
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ (U y : Set X) := by
    simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩
