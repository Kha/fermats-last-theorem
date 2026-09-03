import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_residue_eq_one_of_pow_prime_pow_eq_one
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.residue_eq_one_of_pow_prime_pow_eq_one
    (P : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p)
    {ζ : AlgebraicClosure ℚ} {n : ℕ} (hζ : ζ ^ p ^ n = 1) (hζP : ζ ∈ P) :
    IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_residue_eq_one_of_pow_prime_pow_eq_one.solution
