module

public import Definitions.Def_AlgebraicCurve_PlacesOverDVR
public import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_exists_restrict_eq

set_option autoImplicit false
noncomputable section
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_restrict_eq.AlgebraicCurve IsDedekindDomain"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "fiberOver restrict_eq_of_mem_fiberOver restrict sum_ramificationIndex_mul_inertiaDeg_fiberOver"
p2m_open "AlgebraicCurve.Place"

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_exists_restrict_eq.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [Algebra.IsSeparable F' M] (w : Place K F') :
    ∃ W : Place K M, W.restrict F' = w := by
  by_contra hne
  push Not at hne
  have hempty : w.fiberOver M = ∅ :=
    Finset.eq_empty_of_forall_notMem fun W hW => hne W (restrict_eq_of_mem_fiberOver w hW)
  have hsum := sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := M) w
  rw [hempty, Finset.sum_empty] at hsum
  have hpos : 0 < Module.finrank F' M := Module.finrank_pos
  omega

end
