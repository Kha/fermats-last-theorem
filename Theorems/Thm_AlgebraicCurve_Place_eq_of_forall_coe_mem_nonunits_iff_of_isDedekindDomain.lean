import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain

set_option autoImplicit false

theorem AlgebraicCurve.Place.eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain
    {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Subalgebra K F)
    [IsDedekindDomain ↥A] [IsFractionRing ↥A F]
    (v v' : AlgebraicCurve.Place K F)
    (hv : ∀ a : ↥A, (a : F) ∈ v.toValuationSubring) (hv' : ∀ a : ↥A, (a : F) ∈ v'.toValuationSubring)
    (h : ∀ a : ↥A, (a : F) ∈ v.toValuationSubring.nonunits ↔ (a : F) ∈ v'.toValuationSubring.nonunits) :
    v = v' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain.solution
