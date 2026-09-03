import Mathlib
import P2M.Util
namespace P2MW.S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed

set_option autoImplicit false

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  haveI : IsIntegrallyClosed ↥A := inferInstance
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue ↥A) := IsLocalRing.residue_surjective
  obtain ⟨q, hq, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts p).mpr fun n => hsurj (p.coeff n)) hp
  have hdegL : (q.map (algebraMap (↥A) L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective (↥A) L), hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdegL
  have hint : IsIntegral (↥A) x := ⟨q, hmon, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hint
  refine ⟨IsLocalRing.residue (↥A) a, ?_⟩
  have hqa : q.eval a = 0 := by
    apply IsFractionRing.injective (↥A) L
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ha]
    exact hx
  show p.IsRoot (IsLocalRing.residue (↥A) a)
  rw [← hq, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply, hqa, map_zero]
