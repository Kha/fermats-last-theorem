import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_residue_baseGerm_surjective_and_isClosed_crossingPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.residue_baseGerm_surjective_and_isClosed_crossingPt
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hinf : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hzero : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hrat : ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ XO (ΓM M H) hj ρO,
      s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
      s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) :
    (Function.Surjective fun o : O =>
      IsLocalRing.residue ((XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)) (baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) o)) ∧
    IsClosed ({𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n} : Set ↥(XO (ΓM M H) hj ρO)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_residue_baseGerm_surjective_and_isClosed_crossingPt.solution
