import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot

set_option autoImplicit false

theorem AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot
    {H G : Type*} [Group H] [Group G]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ')) :
    typeSubmodule ι ρ ⊓ typeSubmodule ι ρ' = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot.solution
