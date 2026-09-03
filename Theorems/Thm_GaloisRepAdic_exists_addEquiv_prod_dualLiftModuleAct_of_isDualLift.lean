import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem GaloisRepAdic.exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (ρA : GaloisRepAdic (DualNumber k))
    (ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (hframe : ∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
      ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
        Matrix.dualNumberEquiv.symm
          ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
            LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)
    (c : cocycles₁ ρbar.adZero)
    (hc : ∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) :
    ∃ φ : ρA.V ≃+ ρbar.V × ρbar.V,
      ∀ (σ : primeLocalGaloisGroup (pPrime p)) (x : ρA.V),
        φ (ρA.ρ (primeLocalToGlobal (pPrime p) σ) x) =
          ρbar.dualLiftModuleAct p
            (mapCocycles₁ (primeLocalToGlobal (pPrime p))
              (𝟙 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) c) σ (φ x) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift.solution
