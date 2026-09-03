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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_baseChangeEq_of_comp_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_baseChangeEq_of_comp_eq
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S S' : Type} [CommRing S] [CommRing S'] (g : B →+* S) (h : S →+* S') (g' : B →+* S')
    (hg' : h.comp g = g')
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (hc' : t.IsGradedS ι ψ g') (hcb' : t.IsGradedSbar ι ψ g')
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g')
    (hXh : (t.XS g).F.map h = (t.XS g').F)
    (bc : CartierModule p (t.XS g).F →+ CartierModule p (t.XS g').F)
    (hbc : bc = CartierModule.baseChangeEq h hXh)
    (hbcV : ∀ x, bc (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung x) =
      ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').verschiebung (bc x))
    (hbcPi : ∀ x, bc (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi x) =
      ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').varpi (bc x))
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (L' : ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').M →+
      ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').NMod)
    (hL' : ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc').IsCanonicalLMap L')
    (hLL' : ∀ x, L' (bc x) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc') bc hbcV hbcPi (L x))
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v) :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g' hc' hcb' hcΦg' L' hL' i
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t.XS g').toGradedCartierModuleData (Rigidified.jS ι ψ g') hc') bc hbcV hbcPi z) v := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_baseChangeEq_of_comp_eq.solution
