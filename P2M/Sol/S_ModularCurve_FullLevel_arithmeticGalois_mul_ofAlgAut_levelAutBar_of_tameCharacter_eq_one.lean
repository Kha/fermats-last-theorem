import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one
import Theorems.Thm_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul
import P2M.Util
namespace P2MW.S_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve
open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (hτπ : P.tameCharacter π τ = 1) (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ *
        SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) =
      SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) *
        arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ := by
  have hfix : τ ζ.val = ζ.val :=
    ValuationSubring.apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one q P hP π hπ hτ hτπ
      (ζ.isPrimitiveRoot.pow_eq_one)
  have hinv : τ⁻¹ • ζ = ζ := Idx.ext (by
    rw [Idx.val_smul, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact hfix.symm)
  have h := ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul q M' hqM' τ ζ γ hγ
  rwa [hinv] at h
