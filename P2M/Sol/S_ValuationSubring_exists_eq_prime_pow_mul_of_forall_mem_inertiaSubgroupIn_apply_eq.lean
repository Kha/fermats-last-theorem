import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_eq_prime_pow_mul_of_forall_mem_inertiaSubgroupIn_apply_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

theorem solution
    (p : ℕ) (hp : p.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (x : AlgebraicClosure ℚ) (hx0 : x ≠ 0) (hxP : x ∈ P)
    (hxI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x) :
    ∃ (n : ℕ) (u : AlgebraicClosure ℚ), P.valuation u = 1 ∧ (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ u = u) ∧
      x = (p : AlgebraicClosure ℚ) ^ n * u := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨O, hOA, -, hDVR, hirr, hnu, hI, hmem⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p P hP
  haveI := hDVR

  set xO : ↥O := ⟨x, hmem x hxP hxI⟩ with hxO
  have hxO0 : xO ≠ 0 := by
    intro h
    apply hx0
    have := congrArg Subtype.val h
    simpa [hxO] using this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxO0 hirr
  refine ⟨n, ((u : ↥O) : AlgebraicClosure ℚ), ?_, ?_, ?_⟩
  ·
    have hle : P.valuation ((u : ↥O) : AlgebraicClosure ℚ) ≤ 1 :=
      P.valuation_le_one ⟨((u : ↥O) : AlgebraicClosure ℚ), hOA (u : ↥O).prop⟩
    have hge : ¬ P.valuation ((u : ↥O) : AlgebraicClosure ℚ) < 1 :=
      fun hlt => hnu (u : ↥O) hlt (Units.isUnit u)
    exact le_antisymm hle (not_lt.1 hge)
  · intro σ hσ
    exact (hI σ).1 hσ (u : ↥O) (u : ↥O).prop
  · have := congrArg Subtype.val hu

    simp only [hxO, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast] at this
    rw [this, mul_comm]
