import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ).base P.1 ∈ (pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))))
      (n : ℕ) (c : Fin n → ↥(chartAlgInf p (ΓN p M H hpM) hj)) (a : Fin n → IsLocalRing.ResidueField ↥A),
      ((𝔛.Mfib A hA ρ hρ).placeOfPoint P).ord
        (∑ i, algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) (a i) *
          ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
            ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField
              ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                  (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
              (((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                  (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv (c i))))))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf.solution
