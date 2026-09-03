import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_one_of_not_dvd
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import P2M.Util
namespace P2MW.S_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor

set_option autoImplicit false

open WeierstrassCurve

theorem solution (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ ≠ 0 := by
  have hℓ1 : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have hv : A.valuation ((W.Δ : ℤ) : AlgebraicClosure ℚ) = 1 :=
    ValuationSubring.valuation_intCast_eq_one_of_not_dvd A hℓ hℓ1 hgood
  have hmem : ((W.Δ : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A _
  have hunit : IsUnit (⟨_, hmem⟩ : A) := (A.valuation_eq_one_iff _).mpr hv
  have hcast : ((W.Δ : ℤ) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ⟨_, hmem⟩ := by
    rw [show (⟨((W.Δ : ℤ) : AlgebraicClosure ℚ), hmem⟩ : A) = ((W.Δ : ℤ) : A) from
      Subtype.ext (by push_cast; rfl), map_intCast]
  rw [WeierstrassCurve.map_Δ, eq_intCast, hcast]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunit
