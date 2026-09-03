import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (a b : (v.adicCompletion K)ˣ) :
    (∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b)) ↔
      ((∃ α : (L ⊗[K] v.adicCompletion K)ˣ, Algebra.norm (v.adicCompletion K) (α : (L ⊗[K] v.adicCompletion K)) = (a : (v.adicCompletion K))) ∧
        (∃ β : (L ⊗[K] v.adicCompletion K)ˣ, Algebra.norm (v.adicCompletion K) (β : (L ⊗[K] v.adicCompletion K)) = (b : (v.adicCompletion K)))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq.solution
