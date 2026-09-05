module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
public import Mathlib.Data.Int.ConditionallyCompleteOrder
import Definitions.Def_AlgebraicCurve_RatFuncPlaces -- shake: keep

namespace P2MW.S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one

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
private theorem rowMain {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring_priv]
  exact Valuation.mem_valuationSubring_iff _ _

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 :=
  AlgebraicCurve.Place.rowMain v
end S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
end P2MW

public section
open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one AlgebraicCurve.Place.mem_iff_adicValuation_le_one
end
