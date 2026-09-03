import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_finsum_addMonoidHom_conj_T_zpow_eq_zero
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.finsum_addMonoidHom_conj_T_zpow_eq_zero (N : ℕ) [NeZero N] {A : Type*} [AddCommGroup A]
    [IsAddTorsionFree A] (φ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A)
    (u : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(CongruenceSubgroup.Gamma0 N))
    (hu : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ((u q : ↥(CongruenceSubgroup.Gamma0 N)) : SL(2, ℤ)) = q.out⁻¹ * ModularGroup.T ^ (N : ℤ) * q.out) :
    ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, φ (Additive.ofMul (u q)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_finsum_addMonoidHom_conj_T_zpow_eq_zero.solution
