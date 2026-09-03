import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_geomFibreH0Finrank_pos_pullback_of_stage
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isUnit_geomFibreH0Finrank_pos_pullback_of_stage
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (hPOS : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛)
    (𝔭 : PrimeSpectrum S)
    (hpos : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      (∀ s : S, s ∉ 𝔭.asIdeal → sk s ≠ 0) → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk),
      ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), sk g ≠ 0 → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk))
    (𝔭 : PrimeSpectrum S)
    (g₀ : S) (hg₀ : g₀ ∉ 𝔭.asIdeal) (ψ : Localization.Away g₀ →+* Localization.AtPrime 𝔭.asIdeal)
    (hψ : ψ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S (Localization.AtPrime 𝔭.asIdeal))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))).Modules)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (hK : ∀ (L' : RelativeGroupLaw (Localization.Away g₀) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g₀)))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelIsTwoTorsion (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜)
    (hpos𝔭 : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : (Localization.AtPrime 𝔭.asIdeal) →+* k),
      0 < Scheme.Modules.geomFibreH0Finrank (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
        ((Scheme.Modules.pullback (pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ Spec.map (CommRingCat.ofHom ψ))
              (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ⟶
                pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))).obj 𝓜) k sk) :
    ∃ s : S, s ∉ 𝔭.asIdeal ∧
      ∀ (Y : Type) [CommRing Y] [Algebra S Y] (_ : IsUnit (algebraMap S Y (g₀ * s)))
        (φ : (Localization.Away g₀) →+* Y) (_ : φ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S Y)
        (ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
        (_ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
        (_ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ≫ Spec.map (CommRingCat.ofHom φ))
        (k : Type) [Field k] [IsAlgClosed k] (sk : Y →+* k),
        0 < Scheme.Modules.geomFibreH0Finrank (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) ((Scheme.Modules.pullback ρ).obj 𝓜) k sk := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_geomFibreH0Finrank_pos_pullback_of_stage.solution
