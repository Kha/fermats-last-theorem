import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow

set_option autoImplicit false

open TensorProduct

universe u v w

theorem AlgebraicGeometry.AdmissibleAlgebra.exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow
    {R : Type u} [CommRing R] {G : Type v} [Group G] [Finite G] [MulSemiringAction G R]
    (t : R) (ht : ∀ g : G, g • t = t) (ht0 : ∀ x : R, t * x = 0 → x = 0) (e : ℕ)
    (hH1 : ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k * y g = g • z - z) → ∃ z : R, ∀ g : G, t ^ e * y g = g • z - z)
    (m : ℕ) (hm : e ≤ m) (x : R) (hx : ∀ g : G, g • x - x ∈ Ideal.span {t ^ m}) :
    ∃ w : R, (∀ g : G, g • w = w) ∧ x - w ∈ Ideal.span {t ^ (m - e)} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow.solution
