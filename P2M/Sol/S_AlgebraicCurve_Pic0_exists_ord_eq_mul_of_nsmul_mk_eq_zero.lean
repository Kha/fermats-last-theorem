import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Pic0_exists_ord_eq_mul_of_nsmul_mk_eq_zero

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : ↥(Divisor.degZero (K := K) (F := F))) (n : ℕ) (h : n • Pic0.mk D = 0) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by
  have hmk : ∀ m : ℕ, Pic0.mk (m • D) = m • Pic0.mk D := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [succ_nsmul, Pic0.mk_add, ih, succ_nsmul]
  have h1 : Pic0.mk (n • D) = 0 := by rw [hmk, h]
  have h2 : (n • D : ↥(Divisor.degZero (K := K) (F := F))) ∈
      (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨f, hf, hfD⟩ := (Divisor.mem_principal.mp h2)
  refine ⟨f, hf, fun v => ?_⟩
  rw [← hfD v, AddSubgroupClass.coe_nsmul, Finsupp.coe_nsmul, Pi.smul_apply, nsmul_eq_mul]
