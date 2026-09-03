import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (p₁ p₂ : (L ⊗[K] v.adicCompletion K)ˣ) (x k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    AutomorphicForm.semiLocalWeight K L v (diagUnits2 p₁ p₂ * x * k) = AutomorphicForm.semiLocalWeight K L v x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet.solution
