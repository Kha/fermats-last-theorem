import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn

set_option autoImplicit false

theorem IsLocalRing.maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn
    (O : Type) [CommRing O] [IsLocalRing O]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    (res : R →+* IsLocalRing.ResidueField O) (hres : res.comp (algebraMap O R) = IsLocalRing.residue O)
    (s : Set R) (hs : s ⊆ IsLocalRing.maximalIdeal R)
    (hsep : ∀ χ χ' : R →+* DualNumber (IsLocalRing.ResidueField O),
      ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).toRingHom.comp χ = res ∧ χ.comp (algebraMap O R) = (algebraMap (IsLocalRing.ResidueField O) (DualNumber (IsLocalRing.ResidueField O))).comp (IsLocalRing.residue O)) →
      ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).toRingHom.comp χ' = res ∧ χ'.comp (algebraMap O R) = (algebraMap (IsLocalRing.ResidueField O) (DualNumber (IsLocalRing.ResidueField O))).comp (IsLocalRing.residue O)) →
      (∀ x ∈ s, χ x = χ' x) → χ = χ') :
    IsLocalRing.maximalIdeal R =
      (IsLocalRing.maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span s ⊔ (IsLocalRing.maximalIdeal R) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn.solution
