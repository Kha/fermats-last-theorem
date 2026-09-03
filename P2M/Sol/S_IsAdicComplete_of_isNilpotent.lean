import Mathlib
import P2M.Util
namespace P2MW.S_IsAdicComplete_of_isNilpotent

set_option autoImplicit false

universe u v

open IsLocalRing

theorem solution {R : Type u} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) :
    IsAdicComplete I R := by
  obtain ⟨N, hN⟩ := hI
  haveI : IsHausdorff I R := ⟨fun x hx => by
    have h := hx N
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hN] at h
    exact h⟩
  haveI : IsPrecomplete I R := ⟨fun {f} hf => ⟨f N, fun n => by
    rcases le_or_gt n N with hn | hn
    · exact hf hn
    · have hzero : (I ^ n • ⊤ : Ideal R) = ⊥ := by
        rw [smul_eq_mul, Ideal.mul_top, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
        exact Ideal.pow_le_pow_right hn.le
      rw [SModEq.sub_mem, hzero, Ideal.mem_bot, sub_eq_zero]
      have h := hf hn.le
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hN, Ideal.zero_eq_bot, Ideal.mem_bot,
        sub_eq_zero] at h
      exact h.symm⟩⟩
  exact ⟨⟩
