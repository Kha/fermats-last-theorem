import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import P2M.Util
namespace P2MW.S_TateModule_nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow

set_option autoImplicit false

open Submodule

namespace TateFreeR

variable {p : ℕ} {M : Type} [AddCommGroup M] [Fact p.Prime]

theorem finite_torsionBy_r {r : ℕ} (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (n : ℕ) : Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard n]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

theorem mulP_surjective_r {r : ℕ} (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (n : ℕ) : Function.Surjective (TateModule.mulP p M n) := by
  haveI := finite_torsionBy_r hcard (n + 1)
  haveI := finite_torsionBy_r hcard n
  have hker : Nat.card (TateModule.mulP p M n).ker = p ^ r := by
    rw [Nat.card_congr (TateModule.kerMulPEquiv p M n), hcard 1, pow_one]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (TateModule.mulP p M n).ker
  rw [hcard (n + 1), Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (TateModule.mulP p M n)).toEquiv,
    hker] at h
  have hrange : Nat.card (TateModule.mulP p M n).range = Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) := by
    rw [hcard n]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos r) ?_
    rw [← h]; ring
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_card_eq _ hrange

end TateFreeR

open TateFreeR in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    Nonempty (Module.Basis (Fin r) ℤ_[p] (TateModule p M)) ∧
    ∀ (n : ℕ) (m : M), ((p ^ n : ℕ) : ℤ) • m = 0 → ∃ x : TateModule p M, (x : ℕ → M) n = m := by
  refine ⟨TateModule.nonempty_basis_of_card_torsionBy p r hcard, fun n m hm => ?_⟩
  have hm' : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) := (mem_torsionBy_iff _ _).2 hm
  choose next hnext using fun k (m : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)) => mulP_surjective_r hcard k m
  refine ⟨⟨TateModule.liftFun next n ⟨m, hm'⟩,
    TateModule.liftFun_mem (fun k m => congrArg Subtype.val (hnext k m)) n ⟨m, hm'⟩⟩, ?_⟩
  change TateModule.liftFun next n ⟨m, hm'⟩ n = m
  rw [TateModule.liftFun_of_le le_rfl, TateModule.coe_liftAux_congr (Nat.sub_self n)]
  rfl
