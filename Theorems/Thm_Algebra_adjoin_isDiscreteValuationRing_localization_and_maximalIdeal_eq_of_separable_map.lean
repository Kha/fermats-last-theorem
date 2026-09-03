import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_adjoin_isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map

set_option autoImplicit false

theorem Algebra.adjoin.isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
    {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing M] [IsDomain M] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (e : M) (f : Polynomial O) (hf : f.Monic) (hfe : Polynomial.aeval e f = 0)
    (hsep : (f.map (IsLocalRing.residue O)).Separable)
    (P : Ideal ↥(Algebra.adjoin O ({e} : Set M))) [P.IsPrime]
    (hP : (IsLocalRing.maximalIdeal O).map (algebraMap O ↥(Algebra.adjoin O ({e} : Set M))) ≤ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        ((IsLocalRing.maximalIdeal O).map (algebraMap O ↥(Algebra.adjoin O ({e} : Set M)))).map
          (algebraMap ↥(Algebra.adjoin O ({e} : Set M)) (Localization.AtPrime P)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_adjoin_isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map.solution
