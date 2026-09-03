import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (t z : F)
    (h : ∀ v : AlgebraicCurve.Place K F, t ∈ v.toValuationSubring → z ∈ v.toValuationSubring) :
    IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring.solution
