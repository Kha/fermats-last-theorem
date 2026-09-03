import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (hτπ : P.tameCharacter π τ = 1) (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ *
        SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) =
      SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) *
        arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one.solution
