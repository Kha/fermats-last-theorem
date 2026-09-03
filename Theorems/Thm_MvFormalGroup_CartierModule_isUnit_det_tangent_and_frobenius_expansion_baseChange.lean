import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.isUnit_det_tangent_and_frobenius_expansion_baseChange
    (p : ℕ) [Fact p.Prime] {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (f i) k).det)
    (c : ℕ → Fin d → Fin d → R)
    (hc : ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.frobenius (f i) =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ j : Fin d, MvFormalGroup.CartierModule.homothety (c m i j) (f j))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h) :
    letI : (Φ.map φ).IsComm := MvFormalGroup.isComm_map Φ φ
    IsUnit (Matrix.of fun i k =>
        MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.baseChange φ (f i)) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p (Φ.map φ),
        MvFormalGroup.CartierModule.frobenius (MvFormalGroup.CartierModule.baseChange φ (f i)) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ.map φ)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety (φ (c m i j))
              (MvFormalGroup.CartierModule.baseChange φ (f j)))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ.map φ)))^[N] h := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange.solution
