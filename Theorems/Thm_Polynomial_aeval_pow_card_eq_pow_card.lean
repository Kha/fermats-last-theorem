import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_aeval_pow_card_eq_pow_card

set_option autoImplicit false

open Polynomial
theorem Polynomial.aeval_pow_card_eq_pow_card
    (F : Type) [Field F] [Fintype F] (E : Type) [CommRing E] [Algebra F E] (p : F[X]) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_aeval_pow_card_eq_pow_card.solution
