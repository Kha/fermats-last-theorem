import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BorelSubgroup
import P2M.Util
import P2M.Sol.S_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel
theorem AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
    (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ h : AutomorphicForm.AdelicGL2 (𝓞 K) K,
      φ (AutomorphicForm.globalPoints (𝓞 K) K γ * h) = φ h)
    {γ : Matrix.GeneralLinearGroup (Fin 2) K} (hγ : γ ∈ AutomorphicForm.borelSubgroup K)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.constantTerm
        (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.globalPoints (𝓞 K) K γ * g)
      = AutomorphicForm.constantTerm
          (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup.solution
