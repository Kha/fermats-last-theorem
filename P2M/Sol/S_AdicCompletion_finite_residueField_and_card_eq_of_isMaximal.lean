import Mathlib
import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
import P2M.Util
namespace P2MW.S_AdicCompletion_finite_residueField_and_card_eq_of_isMaximal
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

theorem solution
    (S : Type) [CommRing S] [IsNoetherianRing S] (x : Ideal S) [x.IsMaximal] [Finite (S ⧸ x)]
    (inst : IsLocalRing (AdicCompletion x S)) :
    Finite (@IsLocalRing.ResidueField (AdicCompletion x S) _ inst) ∧
      Nat.card (@IsLocalRing.ResidueField (AdicCompletion x S) _ inst) = Nat.card (S ⧸ x) := by
  classical
  obtain ⟨_, _, _, -, hsurj, hker, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing S x

  let φ : S →+* IsLocalRing.ResidueField (AdicCompletion x S) :=
    (IsLocalRing.residue (AdicCompletion x S)).comp (algebraMap S (AdicCompletion x S))
  let e : (S ⧸ x) ≃+* IsLocalRing.ResidueField (AdicCompletion x S) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  exact ⟨Finite.of_equiv _ e.toEquiv, Nat.card_congr e.toEquiv.symm⟩
