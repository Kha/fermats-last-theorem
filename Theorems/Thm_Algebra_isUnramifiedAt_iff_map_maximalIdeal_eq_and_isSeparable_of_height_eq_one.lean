import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one

set_option autoImplicit false

theorem Algebra.isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Algebra O C] [Module.Finite O C] [NoZeroSMulDivisors O C]
    (P : Ideal C) [P.IsPrime] (hP : P.height = 1)
    [Algebra (Localization.AtPrime (P.under O)) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra (P.under O) P] :
    (P.under O).height = 1 ∧
    IsDiscreteValuationRing (Localization.AtPrime (P.under O)) ∧
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
    (Algebra.IsUnramifiedAt O P ↔
      Ideal.map (algebraMap O (Localization.AtPrime P)) (P.under O) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      Algebra.IsSeparable (P.under O).ResidueField P.ResidueField) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one.solution
