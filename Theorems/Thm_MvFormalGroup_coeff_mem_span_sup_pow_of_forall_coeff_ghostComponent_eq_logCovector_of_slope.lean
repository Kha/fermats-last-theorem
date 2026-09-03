import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope

set_option autoImplicit false
open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞)
    (hφint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * φi.coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (A B C : ℕ) (hAB : A < B)
    (hslope : ∀ m : Fin d →₀ ℕ, m ≠ 0 →
      φi.coeff m ∈ Ideal.span {(p : 𝓞) ^ ((m.degree - 1) - (A * Nat.log p m.degree) / B - C)})
    (E : ℕ) :
    ∃ n₂ : ℕ, ∀ (M : ℕ) (c : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * φi.coeff m) ∧
        (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = φi.coeff m ∨
          (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ φi.coeff m))) →
      ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, j + n₂ < M →
          ℓ.coeff j ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} ⊔
            (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope.solution
