import Mathlib
import P2M.Util
namespace P2MW.S_Polynomial_aeval_pow_card_eq_pow_card

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial

theorem solution
    (F : Type) [Field F] [Fintype F] (E : Type) [CommRing E] [Algebra F E] (p : F[X]) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F := by
  rw [← Polynomial.expand_aeval (Fintype.card F) p x, FiniteField.expand_card, map_pow]
