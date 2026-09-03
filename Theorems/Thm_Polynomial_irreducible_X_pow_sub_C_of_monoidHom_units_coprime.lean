import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime

set_option autoImplicit false

universe u

open Polynomial

theorem Polynomial.irreducible_X_pow_sub_C_of_monoidHom_units_coprime
    {K : Type u} [Field K] {N : ℕ} (hN : 0 < N) {β : K} (hβ : β ≠ 0)
    (φ : Kˣ →* Multiplicative ℤ)
    (hφ : (Multiplicative.toAdd (φ (Units.mk0 β hβ))).natAbs.Coprime N) :
    Irreducible (X ^ N - C β) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime.solution
