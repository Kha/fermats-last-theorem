import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

open MvPowerSeries

universe u

theorem MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one
    {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1) :
    ∃ ψ : Fin d → MvPowerSeries (Fin d) 𝓞,
      (∀ i, (ψ i).constantCoeff = 0) ∧
      (∀ i, subst φ (ψ i) = X i) ∧
      (∀ i, subst ψ (φ i) = X i) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one.solution
