import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
attribute [-simp] FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq

set_option autoImplicit false

universe u

open FormalGroup

theorem FormalGroup.exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
    {R : Type u} [CommRing R] (q : ℕ) [Fact q.Prime]
    (F F' : FormalGroup R) [F.IsComm] [F'.IsComm] (ψ : FormalGroup.LawIso F' F) :
    ∃ w : R, IsUnit w ∧
      PowerSeries.coeff q (F.nthSeries q) - w * PowerSeries.coeff q (F'.nthSeries q) ∈ Ideal.span {(q : R)} := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso.solution
