import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : IsCyclotomicExtension {p} ℚ L) (ζ : L) (_ : IsPrimitiveRoot ζ p)
      (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Algebra A L) (_ : IsFractionRing A L)
      (_ : (p : A) ∈ IsLocalRing.maximalIdeal A) (_ : ∃ z : A, algebraMap A L z = ζ)
      (_ : Algebra A (AlgebraicClosure ℚ)) (_ : Algebra L (AlgebraicClosure ℚ)) (_ : IsScalarTower A L (AlgebraicClosure ℚ)),
      (∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ P) ∧
      (∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ P.valuation (algebraMap A (AlgebraicClosure ℚ) a) < 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime.solution
