import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient

theorem Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient
    (R : Type*) [CommRing R] [IsNoetherianRing R] (q : ℕ) [Fact q.Prime]
    (hRq : Finite (R ⧸ Ideal.span {(q : R)}))
    (I : Ideal R) (hqI : (q : R) ∈ I)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (X ⧸ (I ^ m • (⊤ : Submodule R X))) * q ^ C := by p2m_exact_reverting @_root_.P2MW.S_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient.solution
