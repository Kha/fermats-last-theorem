import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_units_mul_sigmaTensor_eq_of_norm_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_units_mul_sigmaTensor_eq_of_norm_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (x : L ⊗[K] v.adicCompletion K) (hx : Algebra.norm (v.adicCompletion K) x = 1) :
    ∃ y : (L ⊗[K] v.adicCompletion K)ˣ,
      x * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ y = y := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_units_mul_sigmaTensor_eq_of_norm_eq_one.solution
