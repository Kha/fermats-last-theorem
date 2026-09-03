import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule

set_option autoImplicit false

theorem LocalNewvector.exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
    (q : ℕ) [Fact q.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[q]) V] [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (T : V →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hT : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), T (x • v) = x • T v)
    (W : Submodule ℂ V) (hW : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ w ∈ W, x • w ∈ W)
    (hsmooth : ∀ w ∈ W, ∃ U : Subgroup (GL (Fin 2) ℚ_[q]),
      IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧ ∀ u ∈ U, u • w = w)
    (a : ℕ) {v : V} (hv : v ∈ W)
    (hTv : T v ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.PSCarrier q μ₁ μ₂)) :
    ∃ y ∈ W, y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) V ∧ T y = T v := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule.solution
