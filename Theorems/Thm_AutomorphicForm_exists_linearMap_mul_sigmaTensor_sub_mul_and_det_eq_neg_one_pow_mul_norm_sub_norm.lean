import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (A B : (L ⊗[K] v.adicCompletion K)ˣ) :
    ∃ T : (L ⊗[K] v.adicCompletion K) →ₗ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K),
      (∀ x, T x = (A : L ⊗[K] v.adicCompletion K) * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x -
        (B : L ⊗[K] v.adicCompletion K) * x) ∧
      LinearMap.det T = (-1) ^ Module.finrank K L *
        (Algebra.norm (v.adicCompletion K) (B : L ⊗[K] v.adicCompletion K) -
          Algebra.norm (v.adicCompletion K) (A : L ⊗[K] v.adicCompletion K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm.solution
