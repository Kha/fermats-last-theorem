import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_MvFormalGroup_WittPointFamilyInt
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (w : ℕ → Fin d → Fin d → WittVector p R)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, w m i l • f l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    {τ : Type v} [Finite τ] (n : ℕ)
    (v : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ)
    (hv : ∀ j, (n : ℕ∞) ≤ ((MvFormalGroup.CartierModule.presPi f v).val j).order) :
    ∃ (N : ℕ) (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ),
      (∀ (l : Fin d) (k : ℕ), (n : ℕ∞) ≤
        ((v l : WittVector p (MvPowerSeries τ R)).coeff k -
          ((MvFormalGroup.WittLaw.verPt (u l) -
              ∑ i : Fin d, ∑ m ∈ Finset.range N, MvFormalGroup.WittLaw.wittSMulPt (w m i l)
                ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i)) :
              MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order) ∧
      (∀ (i : Fin d) (k : ℕ), (n : ℕ∞) ≤
        ((((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i) :
            MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi.solution
