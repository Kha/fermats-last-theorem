import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] :
    (∀ (w : ℕ) (H : Subgroup (G.Point K w)) (z : G.Point K w),
      (∀ ψ : G'.Point K w, (∀ z' ∈ H, D.pair K w z' ψ = 1) → D.pair K w z ψ = 1) → z ∈ H) ∧
    (∀ (H : ∀ w : ℕ, Subgroup (G.Point K w)),
      (∀ (w : ℕ) (z : G.Point K w), G.pointIncl K w z ∈ H (w + 1) → z ∈ H w) →
      ∀ ψ₁ : G'.Point K 1, (∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) →
        ∃ y : TateModule p (G'.Points K),
          (y : ℕ → G'.Points K) 1 = G'.pointsMkAdd K 1 (Additive.ofMul ψ₁) ∧
          ∀ (w : ℕ) (ψ : G'.Point K w),
            G'.pointsMkAdd K w (Additive.ofMul ψ) = (y : ℕ → G'.Points K) w →
            ∀ z ∈ H w, D.pair K w z ψ = 1) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one.solution
