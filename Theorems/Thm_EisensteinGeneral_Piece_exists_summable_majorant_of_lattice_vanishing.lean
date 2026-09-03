import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import P2M.Util
import P2M.Sol.S_EisensteinGeneral_Piece_exists_summable_majorant_of_lattice_vanishing

set_option autoImplicit false

open NumberField

open scoped Classical in

theorem EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing
    (F : Type) [Field F] [NumberField F] (n : ℕ) (R : ℝ)
    (C : Fin n → ℂ → ℂ) (hC : ∀ j, Continuous (C j))
    (Kf : {ξ : F // ξ ≠ 0} → ℂ) (K₀ : ℝ) (hK : ∀ ξ, ‖Kf ξ‖ ≤ K₀)
    (Jr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
    (hJr : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}), ∃ C₁ c₁ : ℝ, ∃ N₁ : ℕ,
      0 < C₁ ∧ 0 < c₁ ∧ ∀ (s : ℂ) (t : ℝ), ‖s‖ ≤ R → t ≠ 0 →
        ‖Jr j i s t‖ ≤ C₁ * max 1 (|t| ^ (-(N₁ : ℝ))) * Real.exp (-c₁ * |t|))
    (Jc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
    (hJc : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), ∃ C₁ c₁ : ℝ, ∃ N₁ : ℕ,
      0 < C₁ ∧ 0 < c₁ ∧ ∀ (s ζ : ℂ), ‖s‖ ≤ R → ζ ≠ 0 →
        ‖Jc j w s ζ‖ ≤ C₁ * max 1 (‖ζ‖ ^ (-(N₁ : ℝ))) * Real.exp (-c₁ * ‖ζ‖))
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (q : {ξ : F // ξ ≠ 0} → mixedEmbedding.mixedSpace F)
    (α₁ : {w : InfinitePlace F // w.IsReal} → ℝ) (hα₁ : ∀ i, α₁ i ≠ 0)
    (α₂ : {w : InfinitePlace F // w.IsComplex} → ℂ) (hα₂ : ∀ w, α₂ w ≠ 0)
    (hq₁ : ∀ (ξ : {ξ : F // ξ ≠ 0}) (i : {w : InfinitePlace F // w.IsReal}),
      (q ξ).1 i = (mixedEmbedding F ξ.1).1 i * α₁ i)
    (hq₂ : ∀ (ξ : {ξ : F // ξ ≠ 0}) (w : {w : InfinitePlace F // w.IsComplex}),
      (q ξ).2 w = (mixedEmbedding F ξ.1).2 w * α₂ w)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Φ : Fin n → {ξ : F // ξ ≠ 0} → ℂ → ℂ)
    (hΦ0 : ∀ (j : Fin n) (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ξ.1 ∉ I → Φ j ξ s = 0)
    (P : ℝ) (k : ℕ) (hΦ : ∀ (j : Fin n) (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ξ.1 ∈ I →
      ‖Φ j ξ s‖ ≤ P * (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k) :
    ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧ ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R →
      ‖∑ j : Fin n, C j s * Kf ξ
        * (∏ i : {w : InfinitePlace F // w.IsReal}, Jr j i s (-(θr i * (q ξ).1 i)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex}, Jc j w s (-(θc w * (q ξ).2 w)))
        * Φ j ξ s‖ ≤ M ξ := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_Piece_exists_summable_majorant_of_lattice_vanishing.solution
