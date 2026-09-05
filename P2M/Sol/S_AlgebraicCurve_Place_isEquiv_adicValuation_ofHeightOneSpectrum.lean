module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import Definitions.Def_AlgebraicCurve_RatFuncPlaces -- shake: keep

namespace P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ofHeightOneSpectrum"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum adicValuation ofHeightOneSpectrum toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.adicValuation_valuationSubring_priv :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

p2m_export "AlgebraicCurve.Place" "adicValuation_valuationSubring_priv"
private theorem _root_.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq_priv {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring_priv.symm)

p2m_export "AlgebraicCurve.Place" "isEquiv_adicValuation_of_valuationSubring_eq_priv"
section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

private theorem rowMain (w : HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (ofHeightOneSpectrum (K := K) w).adicValuation :=
  (ofHeightOneSpectrum (K := K) w).isEquiv_adicValuation_of_valuationSubring_eq_priv rfl

end OfHeightOneSpectrum

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (Place.ofHeightOneSpectrum (K := K) w).adicValuation :=
  AlgebraicCurve.Place.rowMain (K := K) (F := F) w
end S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum
end P2MW

public section
open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (Place.ofHeightOneSpectrum (K := K) w).adicValuation := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum
end
