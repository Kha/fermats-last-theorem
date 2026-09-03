import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed

set_option autoImplicit false

theorem CerednikDrinfeld.Omega.exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed
    (K : Type) [Field K] [DecidableEq K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (p q : Polynomial K) :
    ∃ (m : ℕ) (L M : Fin m → Finset (K × K)),
      (∀ k, ∀ er ∈ L k, er.2 ≠ 0) ∧ (∀ k, ∀ er ∈ M k, er.2 ≠ 0) ∧
      ∀ u : K, q.eval u ≠ 0 →
        (Valued.v (p.eval u) = Valued.v (q.eval u) ↔
          ∃ k, (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (u - er.1)) ∧ (∀ er ∈ M k, Valued.v (u - er.1) ≤ Valued.v er.2)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed.solution
