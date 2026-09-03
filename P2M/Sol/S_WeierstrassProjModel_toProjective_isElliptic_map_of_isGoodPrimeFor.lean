import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_ratLocalizedAt_isUnit_iff
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor

set_option autoImplicit false

open WeierstrassCurve GaloisRep

private theorem coe_algebraMap_int_ratLocalizedAt (p : ℕ) (n : ℤ) :
    ((algebraMap ℤ (ratLocalizedAt p) n : ratLocalizedAt p) : ℚ) = (n : ℚ) :=
  eq_intCast ((ratLocalizedAt p).subtype.comp (algebraMap ℤ (ratLocalizedAt p))) n

private theorem isUnit_map_Δ_of_isGoodPrimeFor
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    IsUnit (algebraMap ℤ (ratLocalizedAt p) W.Δ) := by
  rw [GaloisRep.ratLocalizedAt.isUnit_iff (Fact.out : p.Prime),
    coe_algebraMap_int_ratLocalizedAt, Rat.num_intCast]
  exact fun h => hgood (Int.natCast_dvd.mpr h)

private theorem isElliptic_map_of_isGoodPrimeFor
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    (W.map (algebraMap ℤ (ratLocalizedAt p))).IsElliptic := by
  rw [isElliptic_iff, map_Δ]
  exact isUnit_map_Δ_of_isGoodPrimeFor W p hgood

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    (W.map (algebraMap ℤ (ratLocalizedAt p))).toProjective.IsElliptic :=
  ⟨(isElliptic_map_of_isGoodPrimeFor W p hgood).isUnit⟩
