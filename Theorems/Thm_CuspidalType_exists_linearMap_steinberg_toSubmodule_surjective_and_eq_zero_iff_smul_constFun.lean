import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun

set_option autoImplicit false

theorem CuspidalType.exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module κ V) (_ : FiniteDimensional κ V)
      (ρ : Representation κ (CuspidalType.GL2 q) V)
      (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V),
      (∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧
      (∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun.solution
