import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_linearEquiv_cechH1_swap

set_option autoImplicit false
universe u v

theorem AlgebraicCurve.exists_linearEquiv_cechH1_swap
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    (S S' : Set (AlgebraicCurve.Place K F)) (D : AlgebraicCurve.Divisor K F) :
    ∃ e : AlgebraicCurve.cechH1 S S' D ≃ₗ[K] AlgebraicCurve.cechH1 S' S D,
      ∀ (f : F) (h : f ∈ AlgebraicCurve.lSpaceOn (S ∩ S') D) (h' : f ∈ AlgebraicCurve.lSpaceOn (S' ∩ S) D),
        e (Submodule.Quotient.mk ⟨f, h⟩) = Submodule.Quotient.mk ⟨f, h'⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_linearEquiv_cechH1_swap.solution
