import Mathlib
import P2M.Util
namespace P2MW.S_CongruenceSubgroup_gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N ℓ : ℕ) [NeZero N]
    (hNℓ : Nat.Coprime N ℓ) :
    CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 ℓ =
      CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · rw [Nat.mul_zero]
  haveI : NeZero ℓ := ⟨hℓ⟩
  ext A
  simp only [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
  constructor
  · rintro ⟨⟨h00, h11, h10⟩, hl⟩
    refine ⟨⟨h00, h11, h10⟩, ?_⟩
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 hl
    have hmul : ((N * ℓ : ℕ) : ℤ) ∣ (↑A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      push_cast
      exact (Nat.isCoprime_iff_coprime.mpr hNℓ).mul_dvd h10 hl
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hmul
  · rintro ⟨⟨h00, h11, h10⟩, hl⟩
    refine ⟨⟨h00, h11, h10⟩, ?_⟩
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hl ⊢
    exact dvd_trans (by push_cast; exact dvd_mul_left _ _) hl
