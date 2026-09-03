import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped TensorProduct

theorem ResidualGaloisRep.exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (χ : primeLocalGaloisGroup (pPrime p) →* Multiplicative (ZMod ℓ)) (hχ : Function.Surjective χ) :
    ∃ (a : primeLocalGaloisGroup (pPrime p) → k)
      (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))),
      (∀ σ, (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ =
          a σ • (1 : Module.End k ρbar.V)) ∧
      (∃ σ, a σ ≠ 0) ∧ (∀ σ τ, a (σ * τ) = a σ + a τ) ∧
      ∃ π : (ZMod ℓ → ρbar.V) →+ ρbar.V × ρbar.V, Function.Surjective π ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (F : ZMod ℓ → ρbar.V),
          π (fun i => ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (F (i - Multiplicative.toAdd (χ σ)))) =
            ρbar.dualLiftModuleActAd p c σ (π F) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd.solution
