import Mathlib
import P2M.Util
import P2M.Sol.S_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot

set_option autoImplicit false

open Polynomial
theorem minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
    (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (m : ℕ) (ζ : E) (hζ : IsPrimitiveRoot ζ m)
    (hm : (Fintype.card F).Coprime m) :
    (minpoly F ζ).natDegree = orderOf (ZMod.unitOfCoprime (Fintype.card F) hm) ∧
    ∀ x : E, Polynomial.aeval x (minpoly F ζ) = 0 ↔ ∃ i : ℕ, x = ζ ^ (Fintype.card F ^ i) := by p2m_exact_reverting @_root_.P2MW.S_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot.solution
