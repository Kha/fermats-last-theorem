import Mathlib
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import P2M.Util
namespace P2MW.S_ModularCurve_phiThree_eq_mul_add_pow_six_mul

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Polynomial ModularCurve

theorem solution :
    phiThree
      = ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3 + 684 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 513 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 27 - (X : Polynomial (Polynomial ℤ))) * ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) - (X : Polynomial (Polynomial ℤ)) ^ 3 + 45 * (X : Polynomial (Polynomial ℤ)) ^ 2 + 216 * (X : Polynomial (Polynomial ℤ)) + 702)
        + 3 ^ 6 * ((-26 + 2545165805037036543 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 621378369711 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 50566 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3)
                   + (2545165805037037030 - 1057401874260783 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 12208810464 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 - 1468 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3) * (X : Polynomial (Polynomial ℤ))
                   + (621378370369 + 12208810635 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 3549914 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 3 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3) * (X : Polynomial (Polynomial ℤ)) ^ 2
                   + (50568 - 1467 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 4 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2) * (X : Polynomial (Polynomial ℤ)) ^ 3) := by
  simp only [phiThree, phiThreeC3, phiThreeC2, phiThreeC1, phiThreeC0, map_add, map_sub, map_neg, map_mul,
    map_pow, map_ofNat]
  ring
