import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq

set_option autoImplicit false

universe u

open IsLocalRing

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Ideal R) (hN : N ≤ maximalIdeal R) (h : maximalIdeal R ≤ N ⊔ maximalIdeal R ^ 2) :
    maximalIdeal R = N := by
  classical
  refine le_antisymm ?_ hN
  have hfg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (N := N) hfg ?_ ?_
  · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  · rw [Ideal.smul_eq_mul, ← pow_two]; exact h
