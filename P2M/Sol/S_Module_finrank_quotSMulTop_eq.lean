import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Theorems.Thm_QuotSMulTop_exists_basis_lift
import P2M.Util
namespace P2MW.S_Module_finrank_quotSMulTop_eq

open scoped Pointwise

theorem solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.finrank (R ⧸ Ideal.span {x}) (QuotSMulTop x M) = Module.finrank R M := by
  haveI := hfree
  haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx) :
          Ideal.span {x} ≤ IsLocalRing.maximalIdeal R)))
  haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
    Module.Finite.of_restrictScalars_finite R _ _
  haveI : Fintype (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :=
    Module.Free.ChooseBasisIndex.fintype _ _
  obtain ⟨b', -⟩ := QuotSMulTop.exists_basis_lift x hx hreg
    (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
  rw [Module.finrank_eq_card_basis b',
    Module.finrank_eq_card_basis
      (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))]
