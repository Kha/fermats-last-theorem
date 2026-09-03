import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic
import P2M.Util
import P2M.Sol.S_Matrix_span_image_map_eq_top_of_span_eq_top

theorem Matrix.span_image_map_eq_top_of_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n]
    {k : Type*} [Field k] {K : Type*} [Field K] (f : k →+* K)
    {S : Set (Matrix n n k)} (hS : Submodule.span k S = ⊤) :
    Submodule.span K ((fun X : Matrix n n k => X.map f) '' S) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_span_image_map_eq_top_of_span_eq_top.solution
