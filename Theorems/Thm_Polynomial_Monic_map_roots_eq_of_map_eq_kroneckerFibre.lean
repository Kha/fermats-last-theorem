import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_Monic_map_roots_eq_of_map_eq_kroneckerFibre

set_option autoImplicit false

open Polynomial
theorem Polynomial.Monic.map_roots_eq_of_map_eq_kroneckerFibre
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (red : A →+* k) (r : L → k) (hr : ∀ a : A, r a = red a)
    {P : Polynomial A} (hP : P.Monic) (a b : k) (hb : b ^ q = a)
    (hred : P.map red = (Polynomial.C (a ^ q) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ q)) :
    ((P.map (algebraMap A L)).roots).map r = {a ^ q} + q • ({b} : Multiset k) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_Monic_map_roots_eq_of_map_eq_kroneckerFibre.solution
