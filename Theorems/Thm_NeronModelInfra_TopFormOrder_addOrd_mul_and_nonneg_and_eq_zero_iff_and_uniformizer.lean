import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] :
    (∀ a b : L, a ≠ 0 → b ≠ 0 → addOrd O L (a * b) = addOrd O L a + addOrd O L b) ∧
    (∀ x : O, 0 ≤ addOrd O L (algebraMap O L x)) ∧
    (∀ x : O, x ≠ 0 → (addOrd O L (algebraMap O L x) = 0 ↔ IsUnit x)) ∧
    (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R' O]
      [IsLocalHom (algebraMap R' O)],
      Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O →
      ∀ π : R', IsLocalRing.maximalIdeal R' = Ideal.span {π} →
        addOrd O L (algebraMap O L (algebraMap R' O π)) = 1) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer.solution
