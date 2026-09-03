import Mathlib
import P2M.Util
import P2M.Sol.S_Subring_exists_valuationSubring_mem_maximalIdeal_iff_apply_eq_zero

set_option autoImplicit false

theorem Subring.exists_valuationSubring_mem_maximalIdeal_iff_apply_eq_zero
    (K Kbar : Type) [Field K] [Field Kbar] [Algebra K Kbar] (B : Subring K)
    (Ω : Type) [Field Ω] (ψ : ↥B →+* Ω) :
    ∃ (O : ValuationSubring Kbar) (hB : ∀ b : ↥B, algebraMap K Kbar (b : K) ∈ O),
      ∀ b : ↥B, (⟨algebraMap K Kbar (b : K), hB b⟩ : ↥O) ∈ IsLocalRing.maximalIdeal ↥O ↔ ψ b = 0 := by p2m_exact_reverting @_root_.P2MW.S_Subring_exists_valuationSubring_mem_maximalIdeal_iff_apply_eq_zero.solution
