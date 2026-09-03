import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn

set_option autoImplicit false

theorem ValuationSubring.surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ) :
    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)
    Function.Surjective toκ ∧ ∀ x : ↥OI, IsUnit x ↔ toκ x ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn.solution
