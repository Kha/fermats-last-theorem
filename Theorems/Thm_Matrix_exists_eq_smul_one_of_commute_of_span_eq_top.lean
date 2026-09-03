import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic
import P2M.Util
import P2M.Sol.S_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top

theorem Matrix.exists_eq_smul_one_of_commute_of_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    {S : Set (Matrix n n A)} (hS : Submodule.span A S = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) :
    ∃ a : A, M = a • 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top.solution
