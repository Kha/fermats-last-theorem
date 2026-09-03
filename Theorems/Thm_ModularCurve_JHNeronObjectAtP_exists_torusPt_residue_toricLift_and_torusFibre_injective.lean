import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_torusPt_residue_toricLift_and_torusFibre_injective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.exists_torusPt_residue_toricLift_and_torusFibre_injective
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) :

    (∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
      ∃ ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
        (∀ v : Fin O.toricRank → ℤ, ψ (AddMonoidAlgebra.single v 1) =
            IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1))) ∧
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA =
          (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre).1 ≫
            pullback.fst O.g (resPt A ≫ Λ.σA)) ∧

    (∀ ψ ψ' : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
      NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre =
        NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ') O.torusFibre → ψ = ψ') ∧

    (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (torusStr (ResidueField ↥A) O.toricRank),
      ∃ ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
        y = torusPt (ResidueField ↥A) O.toricRank ψ) ∧

    NeronModelInfra.schemeHomOverComp
        (torusPt (ResidueField ↥A) O.toricRank
          (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv)
        O.torusFibre = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_torusPt_residue_toricLift_and_torusFibre_injective.solution
