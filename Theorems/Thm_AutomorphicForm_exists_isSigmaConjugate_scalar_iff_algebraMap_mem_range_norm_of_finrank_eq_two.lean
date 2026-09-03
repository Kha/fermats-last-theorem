import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (F : Type) [Field F] [Algebra K F]
    (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a)) :
    (∃ z : (L ⊗[K] F)ˣ, AutomorphicForm.IsSigmaConjugate K L F σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
      algebraMap K F (a : K) ∈
        Set.range (fun x : (L ⊗[K] F)ˣ => Algebra.norm F (x : L ⊗[K] F)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two.solution
