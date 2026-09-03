import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
attribute [-simp] ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

theorem ResidualGaloisRep.baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (K : Type) [Field K] [Algebra k K] (W : Submodule K (ρbar.baseChange K).V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ζ = ζ →
      ∀ x ∈ W, (ρbar.baseChange K).ρ σ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self.solution
