import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem

set_option autoImplicit false

open ModularCurve CongruenceSubgroup open ModularCurve.FullLevel hiding levelAutBar_mul levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_finite_subgroup_forall_levelAutBar_mem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q) :
    ∃ G : Subgroup (fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M'),
      Finite ↥G ∧
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ ∈ G) ∧
      (∀ τ ∈ G, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem.solution
