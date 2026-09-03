import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.LinearAlgebra.UnitaryGroup
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup

open AutomorphicForm.ComplexIwasawa

theorem AutomorphicForm.ComplexIwasawa.kC_mem_specialUnitaryGroup
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    kC g z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.solution
