import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1) :
    ∀ x : AlgebraicClosure ℚ, x ∈ (Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring →
      x ∈ Set.range (algebraMap Rh (AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing.solution
