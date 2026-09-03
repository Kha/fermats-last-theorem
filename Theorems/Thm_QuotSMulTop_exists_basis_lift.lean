import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
import P2M.Sol.S_QuotSMulTop_exists_basis_lift

open scoped Pointwise
theorem QuotSMulTop.exists_basis_lift {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (b : Module.Basis ι (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    ∃ b' : Module.Basis ι R M,
      ∀ i, (Submodule.Quotient.mk (b' i) : QuotSMulTop x M) = b i := by p2m_exact_reverting @_root_.P2MW.S_QuotSMulTop_exists_basis_lift.solution
