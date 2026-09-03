import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul

set_option autoImplicit false

theorem AddMonoidHom.natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul
    {K F M : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup M] [Module F M]
    [Module K M] [IsScalarTower K F M]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (C : M →+ M) (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
    (W : Submodule K M) [FiniteDimensional K W]
    {G : Type*} [AddCommGroup G] (φ : G →+ M) (hφ : Function.Injective φ)
    (hfix : ∀ g : G, C (φ g) = φ g) (hW : ∀ g : G, φ g ∈ W) :
    Finite G ∧ Nat.card G ≤ p ^ Module.finrank K W := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul.solution
