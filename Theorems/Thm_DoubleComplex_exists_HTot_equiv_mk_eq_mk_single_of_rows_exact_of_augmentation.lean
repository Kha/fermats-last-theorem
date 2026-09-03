import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation

set_option autoImplicit false

universe u

theorem DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    (∃ e : LinearMap.ker (dA 0) ≃ₗ[R] DoubleComplex.HTot D 0,
        ∀ (a : A 0) (ha : a ∈ LinearMap.ker (dA 0)),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag 0 => D.C i.1.1 i.1.2) ⟨(0, 0), rfl⟩ (ε 0 a)
              ∈ LinearMap.ker (DoubleComplex.dTot D 0),
            e ⟨a, ha⟩ = Submodule.Quotient.mk ⟨_, hE⟩) ∧
      ∀ n : ℕ, ∃ e : (LinearMap.ker (dA (n + 1)) ⧸
            (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype) ≃ₗ[R] DoubleComplex.HTot D (n + 1),
        ∀ (a : A (n + 1)) (ha : a ∈ LinearMap.ker (dA (n + 1))),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => D.C i.1.1 i.1.2) ⟨(0, n + 1), by omega⟩ (ε (n + 1) a)
              ∈ LinearMap.ker (DoubleComplex.dTot D (n + 1)),
            e (Submodule.Quotient.mk ⟨a, ha⟩) = Submodule.Quotient.mk ⟨_, hE⟩ := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation.solution
