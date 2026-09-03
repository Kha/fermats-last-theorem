import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import P2M.Util
import P2M.Sol.S_Matrix_charpoly_of_uString

set_option autoImplicit false

open Polynomial

theorem Matrix.charpoly_of_uString (F : Type) [Field F] (e : ℕ) (a b : F) :
    (Matrix.of fun i j : Fin (e + 1) =>
        if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
        else (if (i : ℕ) + 1 = (j : ℕ) then (1 : F) else 0)).charpoly =
      if e = 0 then X - C a else X ^ (e - 1) * (X ^ 2 - C a * X + C b) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_charpoly_of_uString.solution
