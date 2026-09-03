import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_natCard_torsion_le_natCard_image_smul_sub_mul_natCard_inertiaInvariants_of_forall_smul_sub_mem_toricPts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.natCard_torsion_le_natCard_image_smul_sub_mul_natCard_inertiaInvariants_of_forall_smul_sub_mem_toricPts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hγI : γ ∈ A.inertiaSubgroupIn ℚ)
    (hγ : ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      x ∈ A.inertiaSubgroupIn ℚ ∧ w ∈ A.inertiaSubgroupIn ℚ ∧ τ = γ ^ j * x ^ (ℓ ^ k) * w ^ (ℓ ^ k))
    (hdisp : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) (ℓ ^ k),
      σ • x - x ∈ O.toricPts (ℓ ^ k)) :
    Nat.card ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) (ℓ ^ k)) ≤
      Nat.card ↥((fun x : JH M H => γ • x - x) ''
          (Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) (ℓ ^ k) : Set (JH M H))) *
        Nat.card ↥{x : JH M H | x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) (ℓ ^ k) ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_natCard_torsion_le_natCard_image_smul_sub_mul_natCard_inertiaInvariants_of_forall_smul_sub_mem_toricPts.solution
