import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_natCard_eq_pow_finrank_span_of_forall_apply_eq_self_of_map_pow_smul

set_option autoImplicit false

theorem AddSubgroup.natCard_eq_pow_finrank_span_of_forall_apply_eq_self_of_map_pow_smul
    {K F M : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup M] [Module F M]
    [Module K M] [IsScalarTower K F M] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (C : M →+ M) (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
    (Y : AddSubgroup M) [Finite Y] (hfix : ∀ y ∈ Y, C y = y) :
    Nat.card Y = p ^ Module.finrank K (Submodule.span K (Y : Set M)) := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_natCard_eq_pow_finrank_span_of_forall_apply_eq_self_of_map_pow_smul.solution
