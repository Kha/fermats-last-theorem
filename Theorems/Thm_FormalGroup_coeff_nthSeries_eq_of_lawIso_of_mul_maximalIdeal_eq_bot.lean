import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.coeff_nthSeries_eq_of_lawIso_of_mul_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥)
    (resT : T →+* k) (hker : RingHom.ker resT = maximalIdeal T)
    (G G' : FormalGroup T) (hG : G.IsBaseChange resT F₀) (hG' : G'.IsBaseChange resT F₀)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈ I) :
    PowerSeries.coeff q (G.nthSeries q) = PowerSeries.coeff q (G'.nthSeries q) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_mul_maximalIdeal_eq_bot.solution
