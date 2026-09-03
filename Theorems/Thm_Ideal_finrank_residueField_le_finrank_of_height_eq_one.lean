import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_finrank_residueField_le_finrank_of_height_eq_one

set_option autoImplicit false

theorem Ideal.finrank_residueField_le_finrank_of_height_eq_one
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C]
    [Algebra O C] [Module.Finite O C] [NoZeroSMulDivisors O C]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁] [Algebra C K] [IsFractionRing C K]
    [Algebra K₁ K] [Algebra O K] [IsScalarTower O K₁ K] [IsScalarTower O C K]
    [FiniteDimensional K₁ K]
    (P : Ideal C) [P.IsPrime] (hP : P.height = 1)
    [Algebra (Localization.AtPrime (P.under O)) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra (P.under O) P] :
    Module.Finite (P.under O).ResidueField P.ResidueField ∧
    Module.finrank (P.under O).ResidueField P.ResidueField ≤ Module.finrank K₁ K := by p2m_exact_reverting @_root_.P2MW.S_Ideal_finrank_residueField_le_finrank_of_height_eq_one.solution
