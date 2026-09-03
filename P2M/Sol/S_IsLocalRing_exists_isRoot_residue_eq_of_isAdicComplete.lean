import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete

set_option autoImplicit false

open Polynomial IsLocalRing in
theorem solution
    {C : Type*} [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    (p : C[X]) (hp : p.Monic) (α : ResidueField C)
    (hα : (p.map (residue C)).IsRoot α) (hα' : ¬ (derivative (p.map (residue C))).IsRoot α) :
    ∃ x : C, p.IsRoot x ∧ residue C x = α := by
  obtain ⟨a₀, rfl⟩ := residue_surjective α
  have hev : ∀ q : C[X], residue C (q.eval a₀) = (q.map (residue C)).eval (residue C a₀) := fun q => by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have h₁ : p.eval a₀ ∈ maximalIdeal C := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    show residue C (p.eval a₀) = 0
    rw [hev]
    exact hα
  have h₂ : IsUnit (Ideal.Quotient.mk (maximalIdeal C) (p.derivative.eval a₀)) := by
    show IsUnit (residue C (p.derivative.eval a₀))
    rw [hev, ← Polynomial.derivative_map, isUnit_iff_ne_zero]
    exact hα'
  obtain ⟨a, ha, hamem⟩ := HenselianRing.is_henselian p hp a₀ h₁ h₂
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hamem
