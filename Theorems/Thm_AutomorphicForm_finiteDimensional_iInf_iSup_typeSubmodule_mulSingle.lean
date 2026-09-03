import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle

set_option autoImplicit false

theorem AutomorphicForm.finiteDimensional_iInf_iSup_typeSubmodule_mulSingle
    {Pl : Type*} [Fintype Pl] [DecidableEq Pl] {K : Pl → Type*} [∀ w, Group (K w)]
    {ι : Pl → Type*} [∀ w, Fintype (ι w)]
    {W : ∀ w, ι w → Type*} [∀ w i, AddCommGroup (W w i)] [∀ w i, Module ℂ (W w i)]
    [∀ w i, FiniteDimensional ℂ (W w i)]
    (ρ : ∀ w i, Representation ℂ (K w) (W w i)) :
    FiniteDimensional ℂ
      ↥(⨅ w, ⨆ i, AutomorphicForm.typeSubmodule (MonoidHom.mulSingle K w) (ρ w i)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle.solution
