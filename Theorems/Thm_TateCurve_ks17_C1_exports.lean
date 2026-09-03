import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab
import P2M.Util
import P2M.Sol.S_TateCurve_ks17_C1_exports

open scoped NNReal
open TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset

theorem TateCurve.ks17_C1_exports.{u_1} :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k)) * q' ^ M)
        (addDefectDiff q' u' v'))
    (hreg : ExpansionRegion q u v),
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (hw0 : w ≠ 0) (d : ℕ),
      Gz w 1 * ∑ j ∈ Finset.range (d / 2), tent w (d - 1 - 2 * j) = ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz w (i : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (n : ℕ),
      xCoeff w n = ∑ f ∈ n.divisors, (f : K) * Fz w (f : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      svComplex u v M = (∑ e ∈ M.divisors, 2 * (e : K) * (∑ i ∈ Finset.range e, ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j)) - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) - (∑ d ∈ M.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))) + (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j))) + Gz u (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))) - ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v (d : ℤ) * xCoeff v (M - a)) + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)) * (Gz u (d : ℤ) * xCoeff u (M - a)))) ∧

    (∀ (d : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1),
      Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * r ^ k) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M),
      ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 → ∑ j ∈ s M k, a M k j * v ^ j = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {B : ℝ} {d : ℕ} (hB : 0 ≤ B) (c : ℕ → ℕ → K)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {g : K → K → K}
    (hinv : ∀ q w : K, q ≠ 0 → 1 < ‖w‖ → ‖q‖ * ‖w‖ < 1 → g q (q * w) = g q w)
    (hrepr : ∀ q w : K, q ≠ 0 → ‖q‖ < ‖w‖ → ‖q‖ * ‖w‖ < 1 → ‖w‖ ≠ 1 →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ M) (g q w)),
      ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ → ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2) = specAlpha c w M + specTail c w M + specGamma c M) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_ks17_C1_exports.solution
