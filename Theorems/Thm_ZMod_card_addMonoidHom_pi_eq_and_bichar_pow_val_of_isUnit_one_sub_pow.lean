import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk

set_option autoImplicit false

open scoped BigOperators

theorem ZMod.card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {R : Type*} [CommRing R] (ζ : Rˣ) (hζ : (ζ : R) ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : R) ^ j)) :
    Nat.card (((i : Fin g) → ZMod (δ i)) →+ ZMod d) = Nat.card ((i : Fin g) → ZMod (δ i)) ∧
    (∀ (h₁ h₂ : (i : Fin g) → ZMod (δ i)) (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
      ζ ^ (c (h₁ + h₂)).val = ζ ^ (c h₁).val * ζ ^ (c h₂).val) ∧
    (∀ (h : (i : Fin g) → ZMod (δ i)) (c₁ c₂ : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
      ζ ^ ((c₁ + c₂) h).val = ζ ^ (c₁ h).val * ζ ^ (c₂ h).val) ∧
    (∀ h : (i : Fin g) → ZMod (δ i), h ≠ 0 → ∃ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, IsUnit ((ζ ^ (c h).val : R) - 1)) ∧
    (∀ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, c ≠ 0 → ∃ h : (i : Fin g) → ZMod (δ i), IsUnit ((ζ ^ (c h).val : R) - 1)) := by p2m_exact_reverting @_root_.P2MW.S_ZMod_card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow.solution
