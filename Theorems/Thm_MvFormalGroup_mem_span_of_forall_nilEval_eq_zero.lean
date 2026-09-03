import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero

set_option autoImplicit false

theorem MvFormalGroup.mem_span_of_forall_nilEval_eq_zero
    {B : Type} [CommRing B] [IsNoetherianRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
    (S : Set (MvPowerSeries σ B)) (G : MvPowerSeries σ B)
    (hG : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : σ → C, (∀ i, s i ∈ J) → (∀ φ ∈ S, MvFormalGroup.nilEval n φ s = 0) → MvFormalGroup.nilEval n G s = 0) :
    G ∈ Ideal.span S := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero.solution
