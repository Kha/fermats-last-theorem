import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Divisor k F) (v : ι → Place k F) (hv : Function.Injective v) (t : ι → F)
    (ht : ∀ i, t i ≠ 0 ∧ (v i).ord (t i) = E (v i))
    (hstep : ∀ i, ∃ g ∈ riemannRochSpace (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) 1),
      g ∉ riemannRochSpace (E - ∑ j, Finsupp.single (v j) 1))
    (c : ι → k) :
    ∃ p ∈ riemannRochSpace E, ∀ i, (v i).HasValue (t i * p) (c i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem.solution
