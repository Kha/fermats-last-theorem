import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_equiv_of_rows_exact_of_augmentation
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    Nonempty (DoubleComplex.HTot D 0 ≃ₗ[R] LinearMap.ker (dA 0)) ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot D (n + 1) ≃ₗ[R]
        (LinearMap.ker (dA (n + 1)) ⧸ (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype)) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation.solution
