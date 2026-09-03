import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isIntegral_of_forall_mem

set_option autoImplicit false
theorem ValuationSubring.isIntegral_of_forall_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    (V : ValuationSubring K) [Algebra V F] [IsScalarTower V K F] (f : F)
    (h : ∀ B : ValuationSubring F, (∀ x : K, algebraMap K F x ∈ B ↔ x ∈ V) → f ∈ B) :
    IsIntegral V f := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isIntegral_of_forall_mem.solution
