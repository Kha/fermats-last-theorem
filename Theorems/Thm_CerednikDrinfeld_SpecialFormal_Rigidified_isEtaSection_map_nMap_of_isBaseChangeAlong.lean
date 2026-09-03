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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_map_nMap_of_isBaseChangeAlong
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ')
    (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom ((t.map f).Φbar ψ') (t.map f).Xbar (t.map f).ρ)
    {S S' : Type} [CommRing S] [CommRing S'] (g : B →+* S) (g' : B' →+* S') (e : S →+* S')
    (hge : g'.comp f = e.comp g)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (hc' : (t.map f).IsGradedS ι ψ' g') (hcb' : (t.map f).IsGradedSbar ι ψ' g')
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' g')
    (bc : MvFormalGroup.CartierModule p (t.XS g).F →+ MvFormalGroup.CartierModule p ((t.map f).XS g').F)
    (hbc : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' e ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (L' : (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').M →+ (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').NMod) (hL' : (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').IsCanonicalLMap L')
    (hLL' : ∀ x, L' (bc x) = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 (L x))
    (bcbar : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod →+ (((t.map (f : B →+* B')).XbarS g').toGradedCartierModuleData (Rigidified.jSbar ι ψ' g') hcb').NMod)
    (hred : ∀ z, (t.map f).etaRed ι ψ' g' hc' hcb' (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) =
      bcbar (t.etaRed ι ψ g hc hcb z))
    (hrig : ∀ w, (t.map f).rigidNum ι hcΦ rΦ ψ' hOD' g' hcb' hcΦg' w = bcbar (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg w))
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v) :
    (t.map f).IsEtaSection ι hcΦ rΦ ψ' hOD' g' hc' hcb' hcΦg' L' hL' i
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) v := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong.solution
