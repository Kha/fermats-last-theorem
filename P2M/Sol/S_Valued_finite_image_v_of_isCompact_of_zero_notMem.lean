import Mathlib
import P2M.Util
namespace P2MW.S_Valued_finite_image_v_of_isCompact_of_zero_notMem

set_option autoImplicit false

open Topology in

theorem solution
    {R : Type*} [DivisionRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]
    (C : Set R) (hC : IsCompact C) (h0 : (0 : R) ∉ C) :
    ((fun x : R => Valued.v x) '' C).Finite := by
  have hne : ∀ x ∈ C, (Valued.v x : Γ₀) ≠ 0 := by
    intro x hx h
    rw [Valuation.zero_iff] at h
    exact h0 (h ▸ hx)
  obtain ⟨t, -, hcover⟩ :=
    hC.elim_nhds_subcover (fun x => {y : R | Valued.v y = Valued.v x}) fun x hx => Valued.locally_const (hne x hx)
  refine (t.finite_toSet.image fun x : R => Valued.v x).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcover hy)
  exact ⟨x, hx, (hyx : Valued.v y = Valued.v x).symm⟩
