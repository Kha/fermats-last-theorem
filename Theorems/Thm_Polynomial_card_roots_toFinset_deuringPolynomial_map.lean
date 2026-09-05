module

public import Mathlib
public import Definitions.Def_Polynomial_DeuringPolynomial
public import P2M.Util
public import P2M.Sol.S_Polynomial_card_roots_toFinset_deuringPolynomial_map

@[expose] public section

open Polynomial
theorem Polynomial.card_roots_toFinset_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) [IsAlgClosed F]
    [DecidableEq F] [Fact q.Prime] [CharP F q] :
    ((deuringPolynomial q).map (Int.castRingHom F)).roots.toFinset.card = (q - 1) / 2 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_card_roots_toFinset_deuringPolynomial_map.solution
