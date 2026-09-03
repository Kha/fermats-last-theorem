import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    [hint : IsIntegral (XO (ΓM M H) hj ρO)]
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (x : ↥(XO (ΓM M H) hj ρO)) [IsNoetherianRing ((XO (ΓM M H) hj ρO).presheaf.stalk x)]
    (hsp₁ : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ x) (hsp₂ : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ x) :
    (Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∧
    (Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _) ∧
    (∀ 𝔭 : Ideal ((XO (ΓM M H) hj ρO).presheaf.stalk x), 𝔭 ∈ (Ideal.span {((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x)}).minimalPrimes →
      𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∨ 𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)) ∧
    (∀ (𝔭 : Ideal ((XO (ΓM M H) hj ρO).presheaf.stalk x)) [𝔭.IsPrime], 𝔭.height = 1 → ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ 𝔭 →
      𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∨ 𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes.solution
