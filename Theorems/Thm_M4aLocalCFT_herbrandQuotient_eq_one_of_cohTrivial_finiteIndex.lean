import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex

set_option autoImplicit false

theorem M4aLocalCFT.herbrandQuotient_eq_one_of_cohTrivial_finiteIndex
    {M : Type*} [CommGroup M] (D N : M →* M)
    (hDN : ∀ x, D (N x) = 1) (hND : ∀ x, N (D x) = 1)
    (V : Subgroup M) [V.FiniteIndex]
    (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V)
    (h0 : ∀ v ∈ V, D v = 1 → ∃ w ∈ V, N w = v)
    (h1 : ∀ v ∈ V, N v = 1 → ∃ w ∈ V, D w = v) :
    Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) =
      Nat.card (N.ker ⧸ (D.range.subgroupOf N.ker)) ∧
    Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex.solution
