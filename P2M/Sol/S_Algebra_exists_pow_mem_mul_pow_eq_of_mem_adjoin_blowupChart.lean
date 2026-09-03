import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_exists_pow_mem_mul_pow_eq_of_mem_adjoin_blowupChart

set_option autoImplicit false

theorem solution
    (C K : Type) [CommRing C] [Field K] [Algebra C K]
    (J : Ideal C) (a : C) (ha : a ∈ J) (ha0 : algebraMap C K a ≠ 0)
    (x : K) (hx : x ∈ Algebra.adjoin C {x : K | ∃ i ∈ J, x * algebraMap C K a = algebraMap C K i}) :
    ∃ (N : ℕ) (g : C), g ∈ J ^ N ∧ x * algebraMap C K a ^ N = algebraMap C K g := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨1, i, by simpa using hi, by simpa using hxi⟩
  | algebraMap r =>
    exact ⟨0, r, by simp, by simp⟩
  | add x y hx' hy' ihx ihy =>
    obtain ⟨N, g, hg, hxg⟩ := ihx
    obtain ⟨N', g', hg', hyg⟩ := ihy
    refine ⟨N + N', g * a ^ N' + g' * a ^ N, ?_, ?_⟩
    · have h1 : g * a ^ N' ∈ J ^ (N + N') := by
        rw [pow_add]; exact Ideal.mul_mem_mul hg (Ideal.pow_mem_pow ha N')
      have h2 : g' * a ^ N ∈ J ^ (N + N') := by
        rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hg' (Ideal.pow_mem_pow ha N)
      exact Ideal.add_mem _ h1 h2
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hxg, ← hyg, pow_add]
      ring
  | mul x y hx' hy' ihx ihy =>
    obtain ⟨N, g, hg, hxg⟩ := ihx
    obtain ⟨N', g', hg', hyg⟩ := ihy
    refine ⟨N + N', g * g', ?_, ?_⟩
    · rw [pow_add]; exact Ideal.mul_mem_mul hg hg'
    · rw [map_mul, ← hxg, ← hyg, pow_add]
      ring
