import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div

set_option autoImplicit false

theorem Subalgebra.le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (J : Ideal ↥C) (t : A)
    (ht0 : algebraMap A K t ≠ 0)
    (B : Subalgebra A K)
    (hB : B = (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K)}).restrictScalars A) :

    C ≤ B ∧

    (∀ b : K, b ∈ B → ∃ n : ℕ, algebraMap A K t ^ n * b ∈ C) ∧

    ((∀ f : K, ∃ g h : ↥C, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) →
      ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) ∧

    (J.FG → Algebra.FiniteType A ↥C → Algebra.FiniteType A ↥B) ∧

    (∀ i : ↥C, i ∈ J → ∃ b : K, b ∈ B ∧ ((i : ↥C) : K) = algebraMap A K t * b) ∧

    (∀ Q : Ideal ↥B, algebraMap A ↥B t ∈ Q →
      ∀ i : ↥C, i ∈ J → ∀ hiB : ((i : ↥C) : K) ∈ B, (⟨((i : ↥C) : K), hiB⟩ : ↥B) ∈ Q) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div.solution
