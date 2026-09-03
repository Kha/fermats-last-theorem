import Mathlib
import Definitions.Def_MvFormalGroup_TwoCocycle
import P2M.Util
import P2M.Sol.S_MvFormalGroup_translate_injective_and_exists_hom_iff_exists_addCoboundary
attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

universe u

theorem MvFormalGroup.translate_injective_and_exists_hom_iff_exists_addCoboundary
    {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm]
    (T : (Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) → Fin n → MvPowerSeries (Fin n ⊕ Fin n) (DualNumber k))
    (hT : ∀ (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) (i : Fin n), T Γ i =
      MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries j))
          fun j => (DualNumber.eps : DualNumber k) •
            MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
        (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i))) :

    (∀ (Γ Γ' : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k),
      (∀ l, MvPowerSeries.constantCoeff (Γ l) = 0) →
      (∀ l, MvPowerSeries.constantCoeff (Γ' l) = 0) →
      (∀ i, T Γ i = T Γ' i) → Γ = Γ') ∧

    (∀ (Γ Γ' : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k),
      (∀ l, MvPowerSeries.constantCoeff (Γ l) = 0) →
      (∀ l, MvPowerSeries.constantCoeff (Γ' l) = 0) →
      ∀ (D D' : MvFormalGroup n (DualNumber k)),
      (∀ i, D.toPowerSeries i = T Γ i) → (∀ i, D'.toPowerSeries i = T Γ' i) →
      ((∃ θ : D.Hom D', ∀ i,
          MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (θ.toPowerSeries i) =
            MvPowerSeries.X i) ↔
        ∃ g : Fin n → MvPowerSeries (Fin n) k, (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
          ∀ l, Γ' l = Γ l + F₀.addCoboundary (g l))) ∧

    (∀ (Γ Γ' : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k),
      (∀ l, MvPowerSeries.constantCoeff (Γ l) = 0) →
      (∀ l, MvPowerSeries.constantCoeff (Γ' l) = 0) →
      ∀ i, T (fun l => Γ l + Γ' l) i +
          MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i) = T Γ i + T Γ' i) ∧

    (∀ (c : k) (μ : DualNumber k →+* DualNumber k),
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp μ = (TrivSqZeroExt.fstHom k k k).toRingHom →
      (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
      ∀ (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k),
      (∀ l, MvPowerSeries.constantCoeff (Γ l) = 0) →
      ∀ i, MvPowerSeries.map μ (T Γ i) = T (fun l => c • Γ l) i) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_translate_injective_and_exists_hom_iff_exists_addCoboundary.solution
