import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime

set_option autoImplicit false

theorem ValuationSubring.mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (C B : Subalgebra R K) (hCB : C ≤ B) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (y : Ideal ↥C) (ϖ : R) (hϖy : algebraMap R ↥C ϖ ∈ y)

    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W ∧ f * (h : K) = (g : K))

    (hcen : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)

    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap R ↥B ϖ ∈ Q →
      (∀ b : ↥C, (⟨(b : K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W → b ∈ Q)

    (τ : K ≃+* K)
    (hC : ∀ a : K, a ∈ C → τ a ∈ C) (hC' : ∀ a : K, a ∈ C → τ.symm a ∈ C)
    (hB : ∀ f : K, f ∈ B → τ f ∈ B) (hB' : ∀ f : K, f ∈ B → τ.symm f ∈ B)
    (hy : ∀ (b : ↥C) (hb : τ (b : K) ∈ C), b ∈ y ↔ (⟨τ (b : K), hb⟩ : ↥C) ∈ y) :
    ∀ f : K, f ∈ W ↔ τ f ∈ W := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime.solution
