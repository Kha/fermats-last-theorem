import Definitions.Def_LocalNewvector_ConductorDatum
import P2M.Util
import P2M.Sol.S_LocalNewvector_exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top

set_option autoImplicit false

theorem LocalNewvector.exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W]
    (hV : LocalNewvector.IsIrreducibleGLRep q V)
    (κ : Type) (f : κ → (V →ₗ[ℂ] W))
    (hf : ∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (v : V), f i (x • v) = x • f i v)
    (hW : ⨆ i : κ, LinearMap.range (f i) = ⊤) :
    ∃ (ι : Type) (L : W →ₗ[ℂ] (ι →₀ V)),
      Function.Injective L ∧ ∀ (x : GL (Fin 2) ℚ_[q]) (w : W), L (x • w) = x • L w := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top.solution
