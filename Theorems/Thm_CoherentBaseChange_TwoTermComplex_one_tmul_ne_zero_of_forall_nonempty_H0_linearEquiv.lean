import Mathlib
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import P2M.Util
import P2M.Sol.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv

set_option autoImplicit false

universe u

open TensorProduct

theorem CoherentBaseChange.TwoTermComplex.one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (g₀ : G.C0)
    (hker : ∀ x : G.C0, G.d x = 0 → ∃ r : R, x = r • g₀)
    (hH0 : ∀ (C : Type u) [CommRing C] [Algebra R C], Nonempty (G.H0 C ≃ₗ[C] C))
    (C : Type u) [CommRing C] [Algebra R C] [Nontrivial C] :
    ((1 : C) ⊗ₜ[R] g₀ : C ⊗[R] G.C0) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.solution
