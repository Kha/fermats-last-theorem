import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card

set_option autoImplicit false

universe u v

theorem MvFormalGroup.End.injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
    (p : ℕ) [Fact p.Prime] {κ : Type u} [Field κ] [Fintype κ] [CharP κ p]
    {k : Type v} [Field k] [CharP k p] (j : WittVector p κ →+* k)
    (G : MvFormalGroup 1 k) [G.IsComm] (ρ : WittVector p κ →+* MvFormalGroup.End G)
    (hρ1 : ∀ a, MvPowerSeries.coeff (Finsupp.single 0 1) ((ρ a).toPowerSeries 0) = j a)
    (hρp : (ρ (p : WittVector p κ)).toPowerSeries 0 =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) k) ^ Fintype.card κ) :
    Function.Injective ρ ∧
      ∀ e : MvFormalGroup.End G, (∀ a, e * ρ a = ρ a * e) → ∃ a, e = ρ a := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.solution
