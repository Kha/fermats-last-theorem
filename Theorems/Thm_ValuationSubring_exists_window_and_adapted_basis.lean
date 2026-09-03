import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_window_and_adapted_basis

set_option autoImplicit false

theorem ValuationSubring.exists_window_and_adapted_basis
    {L : Type*} [Field L] {ι : Type*} (O : Subring L) [IsNoetherianRing O] {r : ℕ}
    (x : Fin r → ι → L)
    (hx : ∀ a : Fin r → L, (∀ n, ∑ i, a i * x i n = 0) → ∀ i, a i = 0)
    (hO : ∀ i n, x i n ∈ O) :
    ∃ (W : Finset ι) (δ : L), δ ∈ O ∧ δ ≠ 0 ∧
      (∀ A : Subring L, O ≤ A → ∀ a : Fin r → L,
          (∀ n ∈ W, ∑ i, a i * x i n ∈ A) → ∀ n, ∑ i, a i * x i n ∈ A) ∧
      ∀ A : ValuationSubring L, O ≤ A.toSubring →
        ∃ (t : Fin r → ι → L) (M M' : Matrix (Fin r) (Fin r) L),
          (∀ j n, t j n = ∑ i, M j i * x i n) ∧ (∀ i n, x i n = ∑ j, M' i j * t j n) ∧
          (∀ j i, δ * M j i ∈ A) ∧ (∀ i j, M' i j ∈ A) ∧
          (∀ a : Fin r → L, (∀ n, ∑ j, a j * t j n ∈ A) → ∀ j, a j ∈ A) ∧
          ∃ ht : ∀ j n, t j n ∈ A,
            LinearIndependent (IsLocalRing.ResidueField A)
              (fun j => fun n : ι => IsLocalRing.residue A ⟨t j n, ht j n⟩) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_window_and_adapted_basis.solution
