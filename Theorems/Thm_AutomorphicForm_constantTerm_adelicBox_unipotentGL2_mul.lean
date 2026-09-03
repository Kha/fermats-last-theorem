import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
attribute [-instance] instCountableOfNumberField_definitions

theorem AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K → ℂ}
    (hφ : ∀ (k : K) (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers K) K
        (AutomorphicForm.unipotentGL2 k) * h) = φ h)
    (x₀ : NumberField.AdeleRing (NumberField.RingOfIntegers K) K)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K) :
    @AutomorphicForm.constantTerm _
        (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
        (@ProbabilityTheory.cond _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.unipotentGL2 x₀ * g)
      = @AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
          (@ProbabilityTheory.cond _
            (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul.solution
