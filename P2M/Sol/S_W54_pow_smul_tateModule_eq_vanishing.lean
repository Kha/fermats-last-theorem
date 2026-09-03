import Definitions.Def_ModularCurve_EichlerShimuraData
import Mathlib.NumberTheory.Padics.RingHoms
import P2M.Util
namespace P2MW.S_W54_pow_smul_tateModule_eq_vanishing

open ModularCurve

theorem solution {p : ℕ} {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    (n : ℕ) {x : ℕ → J} (hx : x ∈ TateModule p J) :
    (∃ y ∈ TateModule p J, (p ^ n : ℕ) • y = x) ↔ x n = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (p ^ n : ℕ) • y n = 0
    exact TateModule.pow_smul_apply hy n
  · intro hxn

    have key : ∀ k m, x m = p ^ k • x (m + k) := by
      intro k
      induction k with
      | zero => intro m; simp
      | succ k ih =>
        intro m
        calc x m = p ^ k • x (m + k) := ih m
          _ = p ^ k • (p • x (m + k + 1)) := by rw [hx.2 (m + k)]
          _ = (p ^ k * p) • x (m + k + 1) := by rw [mul_smul]
          _ = p ^ (k + 1) • x (m + (k + 1)) := by rw [← pow_succ, ← Nat.add_assoc]
    refine ⟨fun m => x (m + n), ⟨?_, fun m => ?_⟩, ?_⟩
    · simpa using hxn
    · have := hx.2 (m + n)
      simpa [Nat.add_right_comm m 1 n] using this
    · funext m
      exact (key n m).symm
