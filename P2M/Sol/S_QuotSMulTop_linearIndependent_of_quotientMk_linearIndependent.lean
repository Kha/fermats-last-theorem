import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
namespace P2MW.S_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent

open scoped Pointwise

theorem solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (m : ι → M) (hli : LinearIndependent (R ⧸ Ideal.span {x}) (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M))) :
    LinearIndependent R m := by
  classical
  have hker_le : LinearMap.ker (Fintype.linearCombination R m) ≤
      Ideal.span {x} • LinearMap.ker (Fintype.linearCombination R m) := by
    intro a ha
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at ha
    have hcoeff : ∀ i, Ideal.Quotient.mk (Ideal.span {x}) (a i) = 0 := by
      have h0 : ∑ i, (Ideal.Quotient.mk (Ideal.span {x}) (a i)) •
          (Submodule.Quotient.mk (m i) : QuotSMulTop x M) = 0 := by
        have hterm : ∀ i, (Ideal.Quotient.mk (Ideal.span {x}) (a i)) •
            (Submodule.Quotient.mk (m i) : QuotSMulTop x M)
            = (Submodule.mkQ (x • ⊤ : Submodule R M)) (a i • m i) := fun i => rfl
        simp_rw [hterm, ← map_sum, ha, map_zero]
      exact Fintype.linearIndependent_iff.mp hli _ h0
    have hdvd : ∀ i, x ∣ a i := fun i =>
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hcoeff i))
    choose c hc using hdvd
    have ha_eq : a = x • c := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact hc i
    have hc_ker : c ∈ LinearMap.ker (Fintype.linearCombination R m) := by
      rw [LinearMap.mem_ker]
      apply hreg
      show x • Fintype.linearCombination R m c = x • (0 : M)
      rw [smul_zero, ← map_smul, ← ha_eq]
      exact ha
    rw [ha_eq]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hc_ker
  have hjac : Ideal.span {x} ≤ Ideal.jacobson ⊥ :=
    le_trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hker : LinearMap.ker (Fintype.linearCombination R m) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _
      (IsNoetherian.noetherian _) hker_le hjac
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg_ker : g ∈ LinearMap.ker (Fintype.linearCombination R m) := by
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact hg
  rw [hker, Submodule.mem_bot] at hg_ker
  exact congrFun hg_ker i
