import Mathlib
import Definitions.Def_GaloisRep_AdZero
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] ResidualGaloisRep.adZeroEquivTraceZero_apply_coe TaylorWiles.mem_traceZero_iff TaylorWiles.adAction_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem ResidualGaloisRep.finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1)
    (hdet : LinearMap.det (ρbar.ρ σ) = -1) :
    Module.finrank k (Rep.res (Subgroup.zpowers σ).subtype ρbar.adZero).ρ.invariants = 1 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one.solution
