import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelJacobian
import Mathlib.FieldTheory.Finite.GaloisField
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.Idx.smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (α : (GaloisField q 2)ˣ) (hα : ι (α : GaloisField q 2) = P.tameCharacter π τ)
    (d : (ZMod q)ˣ) (hd : algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1))
    (ζ : Idx q) :
    τ • ζ = ζ.pow d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ.solution
