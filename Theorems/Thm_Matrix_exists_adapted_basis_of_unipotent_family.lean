import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Valuation.ValuationRing
import P2M.Util
import P2M.Sol.S_Matrix_exists_adapted_basis_of_unipotent_family

theorem Matrix.exists_adapted_basis_of_unipotent_family
    {R : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] (T : Set (Matrix (Fin 2) (Fin 2) R))
    (hmul : ∀ A ∈ T, ∀ B ∈ T, A * B ∈ T)
    (hsq : ∀ A ∈ T, (A - 1) * (A - 1) = 0)
    (A₀ : Matrix (Fin 2) (Fin 2) R) (hA₀ : A₀ ∈ T) (hA₀ne : A₀ ≠ 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧
      (∃ t : R, t ≠ 0 ∧ A₀ * P = P * Matrix.of ![![1, t], ![0, 1]]) ∧
      ∀ A ∈ T, ∃ s : R, A * P = P * Matrix.of ![![1, s], ![0, 1]] := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_adapted_basis_of_unipotent_family.solution
