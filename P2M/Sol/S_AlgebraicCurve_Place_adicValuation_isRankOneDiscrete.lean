module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util

namespace P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete :=
  AlgebraicCurve.Place.rowMain v
end S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.solution
end
