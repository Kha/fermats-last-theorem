import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) :
    ∃ C' : Set (L ⊗[K] v.adicCompletion K)ˣ, IsCompact C' ∧
      ∀ a : (L ⊗[K] v.adicCompletion K)ˣ,
        Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toMonoidHom a * a⁻¹ ∈ C →
        ∃ p : (v.adicCompletion K)ˣ,
          Units.map ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) :
              v.adicCompletion K →* L ⊗[K] v.adicCompletion K) p * a ∈ C' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion.solution
