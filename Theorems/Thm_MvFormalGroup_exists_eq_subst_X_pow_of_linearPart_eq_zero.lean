import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_eq_subst_X_pow_of_linearPart_eq_zero
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_eq_subst_X_pow_of_linearPart_eq_zero
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ} (F : MvFormalGroup n k)
    (φ : Fin n → MvPowerSeries (Fin n) k) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφF : ∀ i, MvPowerSeries.subst F.toPowerSeries (φ i) =
      MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
          fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (F.toPowerSeries i))
    (hlin : MvFormalGroup.linearPart φ = 0) :
    ∃ ψ : Fin n → MvPowerSeries (Fin n) k, (∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) ∧
      ∀ i, φ i = MvPowerSeries.subst (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin n) k) ^ p) (ψ i) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_eq_subst_X_pow_of_linearPart_eq_zero.solution
