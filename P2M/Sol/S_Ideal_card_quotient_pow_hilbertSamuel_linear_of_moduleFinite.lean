import Mathlib
import Theorems.Thm_Submodule_natCard_quotient_pow_smul_top_linear_of_finite_quotient
import P2M.Util
namespace P2MW.S_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite

set_option autoImplicit false

theorem solution
    (R : Type*) [CommRing R] [Module.Finite ℤ R]
    (I : Ideal R) (q : ℕ) [Fact q.Prime] (hqI : (q : R) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (R ⧸ I ^ m) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (R ⧸ I ^ m) * q ^ C := by
  have hq : q.Prime := Fact.out

  haveI : IsNoetherianRing R := isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ R)

  haveI : Module.Finite ℤ (R ⧸ Ideal.span {(q : R)}) := Module.Finite.quotient ℤ _
  haveI : AddGroup.FG (R ⧸ Ideal.span {(q : R)}) := Module.Finite.iff_addGroup_fg.1 inferInstance
  have hRq : Finite (R ⧸ Ideal.span {(q : R)}) := by
    refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨q, hq.pos, ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_nsmul, nsmul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

  obtain ⟨e, C, h⟩ :=
    Submodule.natCard_quotient_pow_smul_top_linear_of_finite_quotient R q hRq I hqI R
  refine ⟨e, C, fun m => ?_⟩
  have hm := h m
  rwa [Ideal.smul_eq_mul, Ideal.mul_top] at hm
