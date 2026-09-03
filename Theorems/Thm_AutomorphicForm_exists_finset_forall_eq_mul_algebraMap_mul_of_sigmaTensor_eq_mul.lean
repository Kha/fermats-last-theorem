import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (G₀ : Set (L ⊗[K] v.adicCompletion K)) (hG₀c : IsCompact G₀) (hG₀o : IsOpen G₀)
    (hG₀1 : (1 : L ⊗[K] v.adicCompletion K) ∈ G₀) (hG₀m : ∀ g ∈ G₀, ∀ h ∈ G₀, g * h ∈ G₀)
    (hG₀i : ∀ g ∈ G₀, ∃ h ∈ G₀, g * h = 1) :
    ∃ Fs : Finset (L ⊗[K] v.adicCompletion K), (∀ f ∈ Fs, IsUnit f) ∧
      ∀ c : L ⊗[K] v.adicCompletion K, IsUnit c →
        (∃ g ∈ G₀, AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ c = c * g) →
        ∃ f ∈ Fs, ∃ x : v.adicCompletion K, x ≠ 0 ∧ ∃ g ∈ G₀,
          c = f * algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x * g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.solution
