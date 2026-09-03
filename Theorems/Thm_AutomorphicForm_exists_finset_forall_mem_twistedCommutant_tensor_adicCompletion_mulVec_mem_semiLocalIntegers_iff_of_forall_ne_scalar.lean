import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Topology

open scoped Classical

theorem AutomorphicForm.exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (b : Fin 2 → L) (hb : b ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ x ∈ {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
        x * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)},
        (∀ i, (x.mulVec fun i => b i ⊗ₜ[K] (1 : v.adicCompletion K)) i ∈ AutomorphicForm.semiLocalIntegers K L v) ↔
          (∀ i j, x i j ∈ AutomorphicForm.semiLocalIntegers K L v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar.solution
