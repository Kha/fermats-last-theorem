import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
import P2M.Sol.S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top

open scoped Pointwise
theorem QuotSMulTop.span_eq_top_of_span_quotientMk_eq_top {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) {ι : Type*} (m : ι → M) (hspan : Submodule.span (R ⧸ Ideal.span {x}) (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤) :
    Submodule.span R (Set.range m) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top.solution
