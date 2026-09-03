import Mathlib
import P2M.Util
namespace P2MW.S_Ideal_exists_mem_forall_not_mem_of_forall_not_le

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] (J : Ideal R) (S : Finset (Ideal R))
    (hS : ∀ P ∈ S, P.IsPrime) (h : ∀ P ∈ S, ¬ J ≤ P) :
    ∃ i ∈ J, ∀ P ∈ S, i ∉ P := by
  classical
  by_contra hcon
  push Not at hcon

  have hsub : ((J : Set R) ⊆ ⋃ P ∈ (↑S : Set (Ideal R)), ((id P : Ideal R) : Set R)) := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := hcon x hx
    exact Set.mem_biUnion hP hxP
  rcases S.eq_empty_or_nonempty with hS0 | ⟨P₀, hP₀⟩
  ·
    obtain ⟨P, hP, -⟩ := hcon 0 J.zero_mem
    rw [hS0] at hP; exact absurd hP (Finset.notMem_empty P)
  · obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime P₀ P₀ (fun P hP _ _ => hS P hP)).mp hsub
    exact h P hP hle
