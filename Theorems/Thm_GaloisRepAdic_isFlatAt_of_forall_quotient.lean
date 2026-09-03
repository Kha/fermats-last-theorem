import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_of_forall_quotient

theorem GaloisRepAdic.isFlatAt_of_forall_quotient {A : Type} [CommRing A]
    [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ}
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)).IsFlatAt p) :
    ρ.IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_of_forall_quotient.solution
