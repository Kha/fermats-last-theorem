import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_tateModuleRep_baseChangeAlong_residual_isEquiv

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing
theorem WeierstrassCurve.tateModuleRep_baseChangeAlong_residual_isEquiv (W : WeierstrassCurve ℚ) (p : ℕ)
    [Fact p.Prime]
    (hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p))
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (ι : ZMod p →+* IsLocalRing.ResidueField 𝒪) :
    (((W.tateModuleRep p hcard).baseChangeAlong (GaloisRep.padicIntToRing 𝒪 p hp)
        (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp)).residual).IsEquiv
      ((W.residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_tateModuleRep_baseChangeAlong_residual_isEquiv.solution
