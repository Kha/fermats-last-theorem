import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem WeierstrassCurve.exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (E₀ : WeierstrassCurve k) [E₀.IsElliptic] :
    ∃ c : Fin 5 → k,
      ∀ (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T), I * maximalIdeal T = ⊥ → I ≤ maximalIdeal T →
      ∀ (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
      ∀ (E E' : WeierstrassCurve T), E.map resT = E₀ → E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) →
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed → G'.toPowerSeries = E'.formalGroupLawFixed →
      ∀ (t : Fin 5 → T), (∀ i, resT (t i) = c i) →
        PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) =
          t 0 * (E'.a₁ - E.a₁) + t 1 * (E'.a₂ - E.a₂) + t 2 * (E'.a₃ - E.a₃) + t 3 * (E'.a₄ - E.a₄) +
            t 4 * (E'.a₆ - E.a₆) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot.solution
