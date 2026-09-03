import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (M : ℕ) (hM : 1 ≤ M) (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ M → G.coeff m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
      (M < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) :
    (∀ μ : (Fin d ⊕ Fin d) →₀ ℕ,
        (subst F.toPowerSeries G
          - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
          - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G).coeff μ ≠ 0 →
        p ^ (M - 1) < μ.degree) ∧
    (∀ (μ : (Fin d ⊕ Fin d) →₀ ℕ) (t : Fin d ⊕ Fin d),
        ((μ t : ℕ) : 𝓞) *
          (subst F.toPowerSeries G
            - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
            - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G).coeff μ ∈
          Ideal.span {(p : 𝓞) ^ (M - 1)}) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc.solution
