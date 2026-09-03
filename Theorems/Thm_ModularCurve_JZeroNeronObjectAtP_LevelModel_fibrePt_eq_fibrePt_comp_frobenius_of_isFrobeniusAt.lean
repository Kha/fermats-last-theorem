import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ValuationSubring_ReduceAt
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.DRLevel IsLocalRing ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p]
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ p)
    (xA zA : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p))
    (h : barPt A ≫ zA.1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A ≫ xA.1) :
    letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
    letI := instDecidableEqResidueFieldSemistable A
    (pullback.lift (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ zA.1) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
        (by rw [Category.assoc, zA.2, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
        Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))) =
      pullback.lift (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
          (by rw [Category.assoc, xA.2, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) ≫
        𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt.solution
