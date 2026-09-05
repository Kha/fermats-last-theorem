module

public import Mathlib
public import Definitions.Def_ModularCurve_JqCoeff
public import Definitions.Def_ModularCurve_SupersingularModuli
public import Definitions.Def_ModularCurve_JWidth
import P2M.Util
import P2M.Sol.S_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one

@[expose] public section
attribute [-instance] ModularCurve.instIsElliptic_tateLaurent
attribute [-simp] ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve
theorem ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)) ^ (q - 1) *
        ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ (12 / jWidth a) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one.solution
