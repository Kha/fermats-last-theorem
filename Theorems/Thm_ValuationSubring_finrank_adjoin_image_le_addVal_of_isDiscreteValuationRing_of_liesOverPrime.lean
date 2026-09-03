import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime

set_option autoImplicit false

theorem ValuationSubring.finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime
    (p : ℕ) [Fact p.Prime]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (hιP : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1)
    (s : Finset Rh) :
    FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p]
        ((fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x)) '' (↑s : Set Rh))) ∧
      ((Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p]
        ((fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x)) '' (↑s : Set Rh))) : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal Rh (p : Rh) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime.solution
