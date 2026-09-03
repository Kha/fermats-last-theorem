import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_forall_indexTwo_stable_eq_bot_or_top_baseChangeAlong

set_option autoImplicit false
theorem ResidualGaloisRep.forall_indexTwo_stable_eq_bot_or_top_baseChangeAlong
    {k k' : Type} [Field k] [Field k'] (ι : k →+* k') (ρ : ResidualGaloisRep k)
    (h : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρ.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρ.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (K' : Type) [Field K'] [Algebra k' K']
    (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hG : G.index = 2)
    (V : Submodule K' ((ρ.baseChangeAlong ι).baseChange K').V)
    (hV : ∀ σ ∈ G, ∀ x ∈ V, ((ρ.baseChangeAlong ι).baseChange K').ρ σ x ∈ V) :
    V = ⊥ ∨ V = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_forall_indexTwo_stable_eq_bot_or_top_baseChangeAlong.solution
