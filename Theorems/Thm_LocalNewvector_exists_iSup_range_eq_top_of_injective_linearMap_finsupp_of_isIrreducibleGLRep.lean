import Definitions.Def_LocalNewvector_ConductorDatum
import P2M.Util
import P2M.Sol.S_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep

set_option autoImplicit false

theorem LocalNewvector.exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (N : Type) [AddCommGroup N] [Module ℂ N] [DistribMulAction (GL (Fin 2) ℚ_[q]) N]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ N]
    (hV : LocalNewvector.IsIrreducibleGLRep q V)
    (ι : Type) (L : N →ₗ[ℂ] (ι →₀ V)) (hL : Function.Injective L)
    (hLx : ∀ (x : GL (Fin 2) ℚ_[q]) (n : N), L (x • n) = x • L n) :
    ∃ (κ : Type) (f : κ → (V →ₗ[ℂ] N)),
      (∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (v : V), f i (x • v) = x • f i v) ∧
        ⨆ i : κ, LinearMap.range (f i) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep.solution
