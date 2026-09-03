import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
import P2M.Sol.S_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent

open scoped Pointwise
theorem QuotSMulTop.linearIndependent_of_quotientMk_linearIndependent {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (m : ι → M) (hli : LinearIndependent (R ⧸ Ideal.span {x}) (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M))) :
    LinearIndependent R m := by p2m_exact_reverting @_root_.P2MW.S_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent.solution
