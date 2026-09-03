import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_WittPointFamily
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_of_forall_le_order_presPi
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (N : ℕ) (c : Fin N → Fin d → Fin d → R) (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} [Finite τ] (n : ℕ) (hn : n ≤ p ^ N)
    (w : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ)
    (hw : ∀ j, (n : ℕ∞) ≤ ((MvFormalGroup.CartierModule.presPi f w).val j).order) :
    ∃ u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ, ∀ (l : Fin d) (k : ℕ),
      (n : ℕ∞) ≤
        ((w l : WittVector p (MvPowerSeries τ R)).coeff k -
          ((MvFormalGroup.WittLaw.verPt (u l) -
              ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.teichPt (c m i l)
                ((⇑(MvFormalGroup.WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) :
              MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi.solution
