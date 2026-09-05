module

import P2M.Sol.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import P2M.Util
public import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree

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
end S_AlgebraicCurve_Place_exists_restrict_eq
end P2MW

public section
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [Algebra.IsSeparable F' M] (w : Place K F') :
    ∃ W : Place K M, W.restrict F' = w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_restrict_eq.solution
end
