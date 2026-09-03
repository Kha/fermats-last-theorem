import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot

set_option autoImplicit false

universe u

theorem WeierstrassCurve.existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (h2 : IsUnit ((2 : ℕ) : T))
    (x' y' : T') (hE' : (W.map π).toAffine.Equation x' y') (h2' : 2 * y' + (W.map π).a₁ * x' + (W.map π).a₃ = 0) :
    ∃! P : T × T, (π P.1 = x' ∧ π P.2 = y') ∧ W.toAffine.Equation P.1 P.2 ∧ 2 * P.2 + W.a₁ * P.1 + W.a₃ = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot.solution
