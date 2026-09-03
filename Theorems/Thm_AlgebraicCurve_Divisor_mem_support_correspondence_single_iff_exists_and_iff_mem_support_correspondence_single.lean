import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ) (P Q : Place K F) :
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        ∃ R : Place K F', R.restrictAlong φ hφ = P ∧ R.restrictAlong ψ hψ = Q) ∧
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        P ∈ (Divisor.correspondence ψ φ hψ hφ (Finsupp.single Q 1)).support) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single.solution
