import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ G₀ : Set (L ⊗[K] v.adicCompletion K), IsCompact G₀ ∧ IsOpen G₀ ∧ (1 : L ⊗[K] v.adicCompletion K) ∈ G₀ ∧
      (∀ g ∈ G₀, ∀ h ∈ G₀, g * h ∈ G₀) ∧ (∀ g ∈ G₀, ∃ h ∈ G₀, g * h = 1) ∧
      (∀ g ∈ G₀, ‖Algebra.norm (v.adicCompletion K) g‖ = 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion.solution
