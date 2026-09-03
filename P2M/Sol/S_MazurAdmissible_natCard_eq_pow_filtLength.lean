import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
namespace P2MW.S_MazurAdmissible_natCard_eq_pow_filtLength

set_option autoImplicit false

noncomputable section

open MazurAdmissible

theorem solution
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : Nat.card M = q ^ filtLength c := by
  have h : ∀ i : Fin (c.n + 1), Nat.card (c.step i) = q ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [c.hbot]; simp
    | succ i ih =>
      have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        ((c.step i.castSucc).addSubgroupOf (c.step i.succ))
      rw [c.hcard i, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (c.hmono i)).toEquiv, ih] at hmul
      rw [hmul, Fin.val_succ, pow_succ, mul_comm, Fin.val_castSucc]
  have htop := h (Fin.last c.n)
  rw [c.htop, AddSubgroup.card_top, Fin.val_last] at htop
  exact htop
