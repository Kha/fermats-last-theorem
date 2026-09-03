import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal

set_option autoImplicit false

theorem LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ⊆
        {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}) ∧
    (∀ δ : GL (Fin 2) L, δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} →
      ∃ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 ∧
        ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)) ∧
    (∀ t t' : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → ((t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) →
      (({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ∩
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}).Nonempty ↔
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
      ({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ↔
        ∃ ζ : L, ζ ≠ 0 ∧
          ((Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
              Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∨
            (Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ∧
              Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))))) := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal.solution
