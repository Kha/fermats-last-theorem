import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackage_residue_baseGerm_surjective_and_isClosed_crossingPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRModelPackage

theorem ModularCurve.DRModelPackage.residue_baseGerm_surjective_and_isClosed_crossingPt
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n)
    (hrat : ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
        pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
      s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
      s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = 𝔛.crossingPt O κ toκ n) :
    (Function.Surjective fun o : O => IsLocalRing.residue ((baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n))
      (baseGerm O (𝔛.crossingPt O κ toκ n) o)) ∧
    IsClosed ({𝔛.crossingPt O κ toκ n} : Set ↥(baseChangeO p O)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackage_residue_baseGerm_surjective_and_isClosed_crossingPt.solution
