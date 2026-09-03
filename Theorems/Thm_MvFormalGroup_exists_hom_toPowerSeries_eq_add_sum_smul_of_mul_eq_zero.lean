import Mathlib
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero
attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

open MvPowerSeries MvFormalGroup
theorem MvFormalGroup.exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero
    {R : Type} [CommRing R] {d : ℕ} {κ : Type} [Fintype κ]
    (j : κ → R) (hj : ∀ k k', j k * j k' = 0)
    (η : κ → Fin d → MvPowerSeries (Fin d) R) (hη : ∀ k i, constantCoeff (η k i) = 0)
    (F : MvFormalGroup d R) :
    ∃ (F' : MvFormalGroup d R) (Φ : F.Hom F') (Ψ : F'.Hom F),
      (∀ i, Φ.toPowerSeries i = X i - ∑ k, j k • η k i) ∧
      (∀ i, Ψ.toPowerSeries i = X i + ∑ k, j k • η k i) ∧
      Ψ.comp Φ = MvFormalGroup.Hom.id F ∧ Φ.comp Ψ = MvFormalGroup.Hom.id F' ∧
      (F.IsComm → F'.IsComm) ∧
      (∀ l, F'.toPowerSeries l = F.toPowerSeries l + ∑ k, j k •
          (∑ i, subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inl i) (F.toPowerSeries l)
          + ∑ i, subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inr i) (F.toPowerSeries l)
          - subst F.toPowerSeries (η k l))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero.solution
