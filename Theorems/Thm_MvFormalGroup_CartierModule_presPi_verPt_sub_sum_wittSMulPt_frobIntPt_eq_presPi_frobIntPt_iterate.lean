import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_MvFormalGroup_WittPointFamilyInt
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ) (N : ℕ)
    (w : Fin N → Fin d → Fin d → WittVector p R)
    (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ l : Fin d, w m i l • f l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ) :
    MvFormalGroup.CartierModule.presPi f
        (fun l => MvFormalGroup.WittLaw.verPt (u l) -
          ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.wittSMulPt (w m i l)
            ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[(m : ℕ)] (u i))) =
      MvFormalGroup.CartierModule.presPi h
        (fun i => (⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate.solution
