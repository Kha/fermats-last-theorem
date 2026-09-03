import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed

set_option autoImplicit false

open Polynomial

universe u v

theorem AlgebraicCurve.exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed
    (K : Type u) [Field K] [IsAlgClosed K] (B : Type v) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra K[X] B] [Module.Finite K[X] B] [FaithfulSMul K[X] B]
    (P : Ideal K[X]) (hP : P.IsMaximal) :
    ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X], z - aeval y q ∈ P • (⊤ : Submodule K[X] B) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed.solution
