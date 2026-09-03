import Mathlib
import P2M.Util
import P2M.Sol.S_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem IsGalois.exists_intermediateField_isPGroup_and_not_dvd_finrank
    (k K : Type*) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] :
    ∃ E : IntermediateField k K, IsPGroup p (K ≃ₐ[↥E] K) ∧ ¬ p ∣ Module.finrank k ↥E := by p2m_exact_reverting @_root_.P2MW.S_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank.solution
