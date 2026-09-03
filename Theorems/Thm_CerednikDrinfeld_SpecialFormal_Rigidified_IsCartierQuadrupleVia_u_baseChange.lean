import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[p] B'] (ψ' : O →+* B')
    (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (σ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (σ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q σ₀ σ₁)
    (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (σ₀' : Q'.T₀ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ')))
    (σ₁' : Q'.T₁ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ')))
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadrupleVia ι hcΦ rΦ ψ' Q' σ₀' σ₁')
    (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁)
    (hτ : (Submodule.span B' (Set.range τ₀) = ⊤) ∧ (Submodule.span B' (Set.range τ₁) = ⊤) ∧
      (∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) ∧ (∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s)))
    (hτσ : (∀ (s : Q.T₀) (i : Fin 2), ((σ₀' (τ₀ s) : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) ∧
      (∀ (s : Q.T₁) (i : Fin 2), ((σ₁' (τ₁ s) : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i))) :
    (∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Q'.N₀ x')
    (tt : Q.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₀ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Q'.u₀ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Q'.N₀ x'))) =
      LocalizedModule.mk (τ₀ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) ∧
    (∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Q'.N₁ x')
    (tt : Q.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₁ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Q'.u₁ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Q'.N₁ x'))) =
      LocalizedModule.mk (τ₁ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange.solution
