import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le
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
    (i : Fin d) (E w : ℕ) :
    ∃ N₁ : ℕ, ∀ N M : ℕ, N₁ ≤ N → N ≤ M →
      ∀ (cN cM : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ N → cN m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
        (N < m.degree → cN m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
          (cN m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → cM m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
        (M < m.degree → cM m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
          (cM m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
      ∀ ℓN ℓM : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < N → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓN).coeff m' = cN (p ^ (N - 1 - n) • m')) →
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓM).coeff m' = cM (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, N - w ≤ j → j < N →
          ℓM.coeff (j + (M - N)) - ℓN.coeff j ∈
            Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} ⊔
              (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le.solution
