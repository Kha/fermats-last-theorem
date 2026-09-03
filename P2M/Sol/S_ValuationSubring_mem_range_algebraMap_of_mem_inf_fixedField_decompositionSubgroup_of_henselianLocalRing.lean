import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup
import Theorems.Thm_RingHom_apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing
import P2M.Util
namespace P2MW.S_ValuationSubring_mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing

set_option autoImplicit false

open IsLocalRing

open ValuationSubring in

theorem solution
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1) :
    ∀ x : AlgebraicClosure ℚ, x ∈ (Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring →
      x ∈ Set.range (algebraMap Rh (AlgebraicClosure ℚ)) := by
  intro x hx
  obtain ⟨E, _, _, ι, φ₀, hι, hφ₀, ⟨e, rfl⟩⟩ :=
    ValuationSubring.exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup p Pl hPl x hx
  exact RingHom.apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing p Pl hPl Rh hRA hRloc E ι hι φ₀ hφ₀ e
