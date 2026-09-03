import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq

set_option autoImplicit false

universe u

theorem MvFormalGroup.Hom.eq_of_forall_subst_curve_eq
    {R : Type u} [CommRing R] {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R)
    (φ ψ : Φ.Hom Φ')
    (h : ∀ γ : Fin d → PowerSeries R, (∀ j, PowerSeries.constantCoeff (γ j) = 0) →
      ∀ k, MvPowerSeries.subst γ (φ.toPowerSeries k) = MvPowerSeries.subst γ (ψ.toPowerSeries k)) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq.solution
