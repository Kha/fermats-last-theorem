import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output

set_option autoImplicit false

open AutomorphicForm WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne
open CongruenceSubgroup
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hρ : Continuous ρ) (hsurj : Function.Surjective ρ)
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g)
    (htame : ∀ q : ℕ, q.Prime → q ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime q)
    (ι : ℤ√(-2) →+* ℂ) (ρℂ : Γℚ →* GL (Fin 2) ℂ)
    (hρℂ : ρℂ = (Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ))
    (N' : ℕ) [NeZero N'] (g : CuspForm (Gamma1 N') 1)
    (hDS : ModularFormClass.qCoeff g 1 = 1 ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N' →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ModularFormClass.qCoeff g p =
                ((ρℂ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
            ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
                ((ρℂ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det *
                  (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
              ModularFormClass.qCoeff g p * ModularFormClass.qCoeff g n) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N' → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) =
          ModularFormClass.qCoeff g ℓ * ModularFormClass.qCoeff g n) ∧
      (∀ ℓ : ℕ, ℓ.Prime →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          (Nat.card ((A.inertiaSubgroupIn ℚ).map ρℂ)).Coprime ℓ →
            N'.factorization ℓ +
                Module.finrank ℂ (Representation.invariants
                  ((Deformation.matrixRepresentation ρℂ).comp
                    (A.inertiaSubgroupIn ℚ).subtype)) = 2 ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
              ∃ hσ : ∀ v ∈ Representation.invariants
                    ((Deformation.matrixRepresentation ρℂ).comp (A.inertiaSubgroupIn ℚ).subtype),
                  Deformation.matrixRepresentation ρℂ σ v ∈ Representation.invariants
                    ((Deformation.matrixRepresentation ρℂ).comp (A.inertiaSubgroupIn ℚ).subtype),
                ModularFormClass.qCoeff g ℓ =
                  LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρℂ σ).restrict hσ)) ∧
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 N' →
        ∀ p : ℕ, p.Prime → ¬ p ∣ N' → ((γ 1 1 : ℤ) : ZMod N') = (p : ZMod N') →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
              ∀ τ : UpperHalfPlane,
                g (γ • τ) =
                  ((ρℂ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det *
                    ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * g τ))) :
    ∃ (N : ℕ) (_ : NeZero N) (b : ℕ → ℤ√(-2)),
      3 ∣ N ∧
      (∀ q : ℕ, q.Prime → q ≠ 3 → ¬ q ^ 3 ∣ N) ∧
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
      CuspForm.IsWeightOneChiNegThreeRealized N b ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ 3 * N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            b p = ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).trace := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output.solution
