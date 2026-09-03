import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint

set_option autoImplicit false

theorem LT.TwistedNorm.setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t tw : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (hN : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (htw : (tw : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (tw : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (htw00 : (tw : Matrix (Fin 2) (Fin 2) L) 0 0 = (t : Matrix (Fin 2) (Fin 2) L) 1 1) (htw11 : (tw : Matrix (Fin 2) (Fin 2) L) 1 1 = (t : Matrix (Fin 2) (Fin 2) L) 0 0) :
    ({γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
      {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)} ∪
        {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ tw⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
    (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ -1 →
      Disjoint {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}
        {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ tw⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
    (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1 →
      {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)} =
        {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ tw⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}) := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint.solution
