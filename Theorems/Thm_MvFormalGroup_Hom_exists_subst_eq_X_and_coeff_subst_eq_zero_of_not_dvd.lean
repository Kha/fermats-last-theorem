import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Hom_exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.Hom.exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) (ψ : Ψ.Hom Φ) :
    ∃ (T : Finset (Fin d)) (Q : Matrix (Fin d) (Fin d) k) (α β : Fin d → MvPowerSeries (Fin d) k),
      T.card = (MvFormalGroup.linearPart ψ.toPowerSeries).rank ∧ IsUnit Q ∧
      (∀ i, (α i).constantCoeff = 0) ∧ (∀ i, (β i).constantCoeff = 0) ∧
      (∀ i, subst α (β i) = X i) ∧ (∀ i, subst β (α i) = X i) ∧
      (∀ i ∈ T, β i = ∑ j, Q i j • ψ.toPowerSeries j) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ), (∃ j ∉ T, ¬ p ∣ m j) →
        coeff m (subst α (ψ.toPowerSeries i)) = 0) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Hom_exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd.solution
