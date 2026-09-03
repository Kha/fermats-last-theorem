import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank

theorem ValuationSubring.finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
    {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    (A : ValuationSubring K) [IsDiscreteValuationRing A]
    [Module.Finite A (integralClosure A F)] :
    {B : ValuationSubring F | ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A}.Finite ∧
    (∀ B : ValuationSubring F, (∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A) →
      IsDiscreteValuationRing B) ∧
    ∑ᶠ B : {B : ValuationSubring F // ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A},
      (letI : Algebra A B.1 := (((algebraMap K F).comp A.subtype).codRestrict B.1
          fun a => (B.2 a).mpr a.2).toAlgebra
       (IsLocalRing.maximalIdeal A).ramificationIdx' (IsLocalRing.maximalIdeal B.1) *
         (IsLocalRing.maximalIdeal A).inertiaDeg' (IsLocalRing.maximalIdeal B.1)) =
      Module.finrank K F := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank.solution
