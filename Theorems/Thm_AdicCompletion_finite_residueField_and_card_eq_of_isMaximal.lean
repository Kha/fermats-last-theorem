import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_finite_residueField_and_card_eq_of_isMaximal
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

theorem AdicCompletion.finite_residueField_and_card_eq_of_isMaximal
    (S : Type) [CommRing S] [IsNoetherianRing S] (x : Ideal S) [x.IsMaximal] [Finite (S ⧸ x)]
    (inst : IsLocalRing (AdicCompletion x S)) :
    Finite (@IsLocalRing.ResidueField (AdicCompletion x S) _ inst) ∧
      Nat.card (@IsLocalRing.ResidueField (AdicCompletion x S) _ inst) = Nat.card (S ⧸ x) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_finite_residueField_and_card_eq_of_isMaximal.solution
