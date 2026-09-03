import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace

set_option autoImplicit false

open WithZero

theorem AlgebraicCurve.exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : AlgebraicCurve.Divisor K F) (T : Finset (AlgebraicCurve.Place K F)) (g : AlgebraicCurve.Place K F → F)
    (hg : ∀ x ∈ T, x.adicValuation (g x) ≤ exp (D x))
    (r : ↥(AlgebraicCurve.adeleSpace K F))
    (hrT : ∀ v ∈ T, (r : AlgebraicCurve.Place K F → F) v = g v) (hr0 : ∀ v ∉ T, (r : AlgebraicCurve.Place K F → F) v = 0)
    (horth : ∀ μ ∈ AlgebraicCurve.omegaSpace (K := K) (F := F) (D - ∑ x ∈ T, Finsupp.single x 1), μ r = 0) :
    ∃ f ∈ AlgebraicCurve.riemannRochSpace (K := K) (F := F) D,
      ∀ x ∈ T, x.adicValuation (f - g x) ≤ exp (D x - 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace.solution
