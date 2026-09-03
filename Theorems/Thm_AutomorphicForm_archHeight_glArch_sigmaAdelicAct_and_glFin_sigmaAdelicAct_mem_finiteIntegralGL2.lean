import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.WindowedSiegel.archHeight L
        (NumberField.AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) =
      AutomorphicForm.WindowedSiegel.archHeight L (NumberField.AdelicLevel.glArch (𝓞 L) L g) ∧
    (NumberField.AdelicLevel.glFin (𝓞 L) L g ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L →
      NumberField.AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) ∈
        NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2.solution
