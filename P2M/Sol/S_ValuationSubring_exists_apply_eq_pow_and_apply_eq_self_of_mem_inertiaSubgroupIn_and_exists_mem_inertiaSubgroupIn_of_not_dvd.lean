import Mathlib
import Mathlib.Data.ZMod.Basic
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd

set_option autoImplicit false

namespace ValuationSubring
p2m_export "ValuationSubring" "algebra valuation LiesOverPrime inertiaSubgroupIn exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn"
namespace PSD
p2m_open "ValuationSubring"

theorem exists_unit_forall_apply_eq_pow (n : ℕ) [NeZero n]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ x : (ZMod n)ˣ, ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ (x : ZMod n).val := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n
  refine ⟨hζ.autToPow ℚ σ, fun μ hμ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, ← hζ.autToPow_spec ℚ σ, pow_right_comm]

end ValuationSubring.PSD

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) (hq : q.Prime) (c N' : ℕ) (hN' : ¬ q ∣ N')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q) :
    (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ x : (ZMod (q ^ c))ˣ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ q ^ c = 1 → σ μ = μ ^ (x : ZMod (q ^ c)).val) ∧
      (∀ μ : AlgebraicClosure ℚ, μ ^ N' = 1 → σ μ = μ)) ∧
    (∀ x : (ZMod (q ^ c))ˣ, ∃ σ ∈ P.inertiaSubgroupIn ℚ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ q ^ c = 1 → σ μ = μ ^ (x : ZMod (q ^ c)).val) ∧
      (∀ μ : AlgebraicClosure ℚ, μ ^ N' = 1 → σ μ = μ)) := by
  haveI : NeZero (q ^ c) := ⟨pow_ne_zero _ hq.ne_zero⟩
  refine ⟨fun σ hσ => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := ValuationSubring.PSD.exists_unit_forall_apply_eq_pow (q ^ c) σ
    exact ⟨x, hx, fun μ hμ =>
      ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn hq P hP hσ hN' hμ⟩
  · obtain ⟨σ, hσ, hx⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one P hq hP c x
    exact ⟨σ, hσ, hx, fun μ hμ =>
      ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn hq P hP hσ hN' hμ⟩
