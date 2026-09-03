import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) :

    (∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A, ∃ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1) ∧

    (∀ (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] ↥A)) (wb wb' : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 →
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ'.ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb')).1 →
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (χ * χ').ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA =
          (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (wb + wb'))).1) ∧

    (∀ (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) (wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 →
        GluedPic0.nodeUnit O.ssFinset wb = 0 →
        ∀ v : Fin O.toricRank → ZMod m, IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single v 1)) = 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one.solution
