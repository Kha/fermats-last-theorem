import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)), ∀ a : (v.adicCompletion K)ˣ, (a : (v.adicCompletion K)) ∈ U → (a : (v.adicCompletion K)) ^ 2 ≠ 1 →
      ∀ γ : GL (Fin 2) (v.adicCompletion K),
        (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          !![(c : (v.adicCompletion K)) * (a : (v.adicCompletion K)), 0; 0, (c : (v.adicCompletion K)) * ((a⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))] →
        ¬ ∃ δ' : GL (Fin 2) (L ⊗[K] v.adicCompletion K), AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.solution
