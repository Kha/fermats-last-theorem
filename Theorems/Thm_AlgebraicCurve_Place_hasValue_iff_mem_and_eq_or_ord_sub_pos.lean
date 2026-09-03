import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos.solution
