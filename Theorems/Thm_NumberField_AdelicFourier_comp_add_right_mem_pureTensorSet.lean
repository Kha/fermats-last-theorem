import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet

open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet
    {F : Type*} [Field F] [NumberField F] (y : AdeleRing (𝓞 F) F)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x => f (x + y)) ∈ pureTensorSet F := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet.solution
