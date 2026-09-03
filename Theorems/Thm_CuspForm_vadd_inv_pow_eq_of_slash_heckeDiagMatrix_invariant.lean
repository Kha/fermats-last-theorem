import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant
attribute [-instance] Ihara.instGroupIharaAmalgam
attribute [-simp] Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups
theorem CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant
    {R q' : ℕ} [NeZero R] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hy : ∀ γ ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q')
    (j : ℕ) (τ : ℍ) :
    y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant.solution
