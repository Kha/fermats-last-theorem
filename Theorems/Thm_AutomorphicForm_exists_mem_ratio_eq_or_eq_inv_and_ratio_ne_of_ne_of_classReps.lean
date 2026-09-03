import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps

set_option autoImplicit false
open NumberField

theorem AutomorphicForm.exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps
    (K : Type) [Field K] [NumberField K]
    (hgenK : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (ΔK : Set (GL (Fin 2) K))
    (hΔKd : ∀ t ∈ ΔK, (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1)
    (hΔKdisj : ∀ t ∈ ΔK, ∀ t' ∈ ΔK, t ≠ t' →
        Disjoint {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
          {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})
    (hΔKcov : {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgenK (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ ΔK, {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})
    :
    (∀ u : Kˣ, (u : K) ≠ 1 →
      ∃ t ∈ ΔK, (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K) ∨
        (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K)⁻¹) ∧
    (∀ t ∈ ΔK, ∀ t' ∈ ΔK, t ≠ t' →
      (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 ≠
          (t' : Matrix (Fin 2) (Fin 2) K) 0 0 / (t' : Matrix (Fin 2) (Fin 2) K) 1 1 ∧
      (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 ≠
          ((t' : Matrix (Fin 2) (Fin 2) K) 0 0 / (t' : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.solution
