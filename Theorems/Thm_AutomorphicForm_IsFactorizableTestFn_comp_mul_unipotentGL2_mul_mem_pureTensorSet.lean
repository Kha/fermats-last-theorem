import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet

theorem AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F]
    {f : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → ℂ}
    (hf : AutomorphicForm.IsFactorizableTestFn F f)
    (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
    (fun s => f (g₁ * AutomorphicForm.unipotentGL2 s * g₂)) ∈ NumberField.AdelicFourier.pureTensorSet F := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet.solution
