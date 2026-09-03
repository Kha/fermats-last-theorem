import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_eq_apOfModel_of_charpoly_frobenius

set_option autoImplicit false
open Polynomial
theorem CuspForm.qCoeff_eq_apOfModel_of_charpoly_frobenius
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (O' : Type) [CommRing O'] [IsLocalRing O'] [CharZero O']
    (iota : chig.range →+* O') (hiota : Function.Injective iota)
    (W : WeierstrassCurve ℤ) (ρ : GaloisRepAdic O')
    (hρg : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X
              + C ((ℓ : O')))
    (hρW : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ (↑S : Set ℕ) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C ((W.apOfModel ℓ : O')) * X + C ((ℓ : O'))) :
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ∉ (↑S : Set ℕ) →
      ModularFormClass.qCoeff g ℓ = (W.apOfModel ℓ : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_eq_apOfModel_of_charpoly_frobenius.solution
