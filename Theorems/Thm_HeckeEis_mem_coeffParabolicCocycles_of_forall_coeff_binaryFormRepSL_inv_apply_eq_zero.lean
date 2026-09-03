import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero
    {K : Type*} [Field K] [CharZero K] (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n)
    {z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (h : ∀ (σ : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N),
      (γ : SL(2, ℤ)) = σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ →
        MvPolynomial.coeff (Finsupp.single 1 n)
          ((HeckeEis.binaryFormRepSL K n σ⁻¹ (z γ) : ↥(HeckeEis.BinaryForm K n)) : MvPolynomial (Fin 2) K) = 0) :
    z ∈ HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero.solution
