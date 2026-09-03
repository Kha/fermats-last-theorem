import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
import P2M.Sol.S_Module_finrank_quotSMulTop_eq

open scoped Pointwise
theorem Module.finrank_quotSMulTop_eq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.finrank (R ⧸ Ideal.span {x}) (QuotSMulTop x M) = Module.finrank R M := by p2m_exact_reverting @_root_.P2MW.S_Module_finrank_quotSMulTop_eq.solution
