import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_iff_exists_isEtaSection_comp
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {B' : Type} [CommRing B'] (g₀ : B →+* B')
    (hOD' : FormalODModule.IsODHom ((t.map g₀).Φbar (g₀.comp ψ)) (t.map g₀).Xbar (t.map g₀).ρ)
    {S : Type} [CommRing S] (h : B' →+* S) (i : Fin 2) (v : Fin 2 → ℚ_[p]) :
    (∃ (hc : (t.map g₀).IsGradedS ι (g₀.comp ψ) h) (hcb : (t.map g₀).IsGradedSbar ι (g₀.comp ψ) h)
        (hcΦh : Rigidified.IsGradedPhiS (Φ := Φ) ι (g₀.comp ψ) h)
        (L : _) (hL : (((t.map g₀).XS h).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, (t.map g₀).IsEtaSection ι hcΦ rΦ (g₀.comp ψ) hOD' h hc hcb hcΦh L hL i z v) ↔
    (∃ (hc : t.IsGradedS ι ψ (h.comp g₀)) (hcb : t.IsGradedSbar ι ψ (h.comp g₀))
        (hcΦh : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (h.comp g₀))
        (L : _) (hL : ((t.XS (h.comp g₀)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (h.comp g₀) hc hcb hcΦh L hL i z v) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp.solution
