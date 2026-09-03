import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem

set_option autoImplicit false

open MvPowerSeries

universe u w

theorem MvFormalGroup.eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))

    (hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (v : ℕ)
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    [IsAdicComplete (Ideal.span {(p : Y)}) Y]
    (ŷ : Fin d → Y) (hŷ : ∀ j, ŷ j ∈ (Ideal.span {(p : Y)}).radical)
    (w' : Fin d → Y)
    (hw' : ∀ j, MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ (F.nthSeries (p ^ v) j) = (p : Y) * w' j)
    (hG : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
        (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
          (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
      MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ G ∈ Ideal.span {(p : Y) ^ N}) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
        MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem.solution
