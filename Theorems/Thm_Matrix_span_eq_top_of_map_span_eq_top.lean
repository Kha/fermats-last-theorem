import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic
import P2M.Util
import P2M.Sol.S_Matrix_span_eq_top_of_map_span_eq_top

theorem Matrix.span_eq_top_of_map_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] [IsLocalRing A]
    {k : Type*} [Field k] (π : A →+* k) (hπ : Function.Surjective π) {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤) :
    Submodule.span A S = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_span_eq_top_of_map_span_eq_top.solution
