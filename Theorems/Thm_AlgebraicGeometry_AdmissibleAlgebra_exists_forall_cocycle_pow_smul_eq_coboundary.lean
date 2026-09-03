import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary

set_option autoImplicit false

open TensorProduct

universe u v w

theorem AlgebraicGeometry.AdmissibleAlgebra.exists_forall_cocycle_pow_smul_eq_coboundary
    {B : Type u} [CommRing B] [IsNoetherianRing B] {R : Type v} [CommRing R] [Algebra B R] [Module.Finite B R]
    {G : Type w} [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G B R] (t : B) :
    ∃ e : ℕ, ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k • y g = g • z - z) → ∃ z : R, ∀ g : G, t ^ e • y g = g • z - z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary.solution
