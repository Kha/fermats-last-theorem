import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Henselian
import P2M.Util
import P2M.Sol.S_Matrix_exists_eigenvalues_of_henselianLocalRing

theorem Matrix.exists_eigenvalues_of_henselianLocalRing {A : Type*} [CommRing A] [IsLocalRing A]
    [HenselianLocalRing A] (M : Matrix (Fin 2) (Fin 2) A) {α β : IsLocalRing.ResidueField A}
    (hne : α ≠ β) (htr : IsLocalRing.residue A M.trace = α + β)
    (hdet : IsLocalRing.residue A M.det = α * β) :
    ∃ a b : A, M.trace = a + b ∧ M.det = a * b ∧ IsUnit (a - b) ∧
      IsLocalRing.residue A a = α ∧ IsLocalRing.residue A b = β := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_eigenvalues_of_henselianLocalRing.solution
