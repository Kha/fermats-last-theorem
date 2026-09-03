import Mathlib
import Definitions.Def_MvFormalGroup_TwoCocycle
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

universe u

open DualNumber in

theorem MvFormalGroup.exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
    {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm]
    (r : ℕ) (Γ : Fin r → MvPowerSeries (Fin n ⊕ Fin n) k) (hΓ : ∀ j, F₀.IsSymmTwoCocycle (Γ j))
    (hspan : ∀ Γ' : MvPowerSeries (Fin n ⊕ Fin n) k, F₀.IsSymmTwoCocycle Γ' →
      ∃ (c : Fin r → k) (g : MvPowerSeries (Fin n) k), MvPowerSeries.constantCoeff g = 0 ∧
        Γ' = ∑ j, c j • Γ j + F₀.addCoboundary g) :
    ∃ (d : ℕ) (D : Fin d → MvFormalGroup n (DualNumber k)),
      d ≤ n * r ∧
      (∀ j, (D j).IsComm ∧ (D j).map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀) ∧
      ∀ (F : MvFormalGroup n (DualNumber k)) [F.IsComm],
        F.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ →
        ∃ (c : Fin d → k) (G : MvFormalGroup n (DualNumber k)) (θ : G.Hom F),
          (∀ i, G.toPowerSeries i =
            MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i) +
              ∑ j, c j • ((D j).toPowerSeries i -
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i))) ∧
          ∀ i, MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (θ.toPowerSeries i) =
            MvPowerSeries.X i := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle.solution
