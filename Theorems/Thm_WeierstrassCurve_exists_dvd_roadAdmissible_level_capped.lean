import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_dvd_roadAdmissible_level_capped

theorem WeierstrassCurve.exists_dvd_roadAdmissible_level_capped (e : ℕ) (p : ℕ) (W : WeierstrassCurve ℤ)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    (M : ℕ) (hM : NeZero M) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S)
    (hMe : ∀ q ∈ S, q ≠ p → ¬ q ^ (e + 1) ∣ M)
    (hMp_ord : (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → ¬ p ^ 2 ∣ M)
    (hMp_flat : W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ M) :
    ∃ N : ℕ, M ∣ N ∧ N ≠ 0 ∧
      (∀ q ∈ S, q.Prime) ∧ p ∈ S ∧
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) ∧
      (∀ q ∈ S, q ≠ p → q ^ e ∣ N) ∧
      (∀ q ∈ S, q ≠ p → ¬ q ^ (e + 1) ∣ N) ∧
      ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → p ∣ N ∧ ¬ p ^ 2 ∣ N) ∧
      (W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ N) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_dvd_roadAdmissible_level_capped.solution
