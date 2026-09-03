import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i : Fin d) (N E : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (c : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
        (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
          (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
      ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, M - N ≤ j → j < M →
          (WittVector.map (MvPowerSeries.substAlgHom
                (MvPowerSeries.hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero)).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inl j) (R := 𝓞)))).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inr j) (R := 𝓞)))).toRingHom ℓ).coeff j ∈
            Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} ⊔
              (Ideal.span (Set.range (X : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) ^ E := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector.solution
