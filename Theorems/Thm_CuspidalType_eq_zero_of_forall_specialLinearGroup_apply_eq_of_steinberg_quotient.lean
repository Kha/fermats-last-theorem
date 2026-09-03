import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspidalType.eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient
    (q : ℕ) [Fact q.Prime]
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) :
    ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient.solution
