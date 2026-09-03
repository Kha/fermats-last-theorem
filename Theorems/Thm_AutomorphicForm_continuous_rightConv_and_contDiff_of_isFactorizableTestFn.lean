import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn

open NumberField
open scoped Classical in

theorem AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    Continuous (rightConv K φ f) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
          rightConv K φ f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn.solution
