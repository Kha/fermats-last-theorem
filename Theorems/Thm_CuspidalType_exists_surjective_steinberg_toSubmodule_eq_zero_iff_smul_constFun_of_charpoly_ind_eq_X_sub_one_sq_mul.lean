import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul

set_option autoImplicit false

open Polynomial

theorem
CuspidalType.exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (κ : Type) [Field κ] [CharP κ p]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)
    (hρ : ∀ g : CuspidalType.GL2 q,
      LinearMap.charpoly (CuspidalType.ind q κ g) = (X - 1) ^ 2 * LinearMap.charpoly (ρ g)) :
    ∃ π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V,
      (∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧
      ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul.solution
