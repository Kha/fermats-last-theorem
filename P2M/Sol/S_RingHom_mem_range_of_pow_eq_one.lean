import Mathlib
import P2M.Util
namespace P2MW.S_RingHom_mem_range_of_pow_eq_one

theorem solution {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ σ.range := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.prim (M := F) (n := n)
  obtain ⟨i, -, hi⟩ := (hζ₀.map_of_injective σ.injective).eq_pow_of_pow_eq_one hζ
  exact ⟨ζ₀ ^ i, by rw [map_pow, hi]⟩
