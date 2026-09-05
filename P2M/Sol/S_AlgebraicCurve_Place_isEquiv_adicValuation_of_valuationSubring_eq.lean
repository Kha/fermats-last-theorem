module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import Definitions.Def_AlgebraicCurve_RatFuncPlaces -- shake: keep

namespace P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum adicValuation toValuationSubring"
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
private theorem rowMain {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring_priv.symm)

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation :=
  AlgebraicCurve.Place.rowMain v h
end S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq
end P2MW

public section
open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq
end
