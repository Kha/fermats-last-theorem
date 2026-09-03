import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one

set_option autoImplicit false

theorem LT.TwistedNorm.exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (hN : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    (∃ Λ : Subgroup (GL (Fin 2) L), ∀ γ : GL (Fin 2) L, γ ∈ Λ ↔ t⁻¹ * (γ * t * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L)) ∧
    ∀ γ : GL (Fin 2) L,
      t⁻¹ * (γ * t * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L) ↔
        (((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)) ∨
        ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 ∧
          σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0) * ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ^ 2 = (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0) := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one.solution
