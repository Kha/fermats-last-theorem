import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical in

theorem NumberField.mixedEmbedding.contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
    (K : Type) [Field K] [NumberField K] :
    (∀ (F : mixedSpace K → ℂ), ContDiff ℝ (⊤ : ℕ∞) F →
      ∀ (C₀ : Set (mixedSpace K)), IsCompact C₀ → (∀ y ∈ C₀, IsUnit y) → (∀ y, F y ≠ 0 → y ∈ C₀) →
        ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => F (Ring.inverse y)) ∧
        IsCompact (Ring.inverse '' C₀) ∧ (∀ y ∈ Ring.inverse '' C₀, IsUnit y) ∧
        ∀ y : mixedSpace K, F (Ring.inverse y) ≠ 0 → y ∈ Ring.inverse '' C₀) ∧
    (∀ (g : mixedSpace K → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) g {y : mixedSpace K | IsUnit y} →
      ∀ (B : (Fin 2 → mixedSpace K) → ℂ), ContDiff ℝ (⊤ : ℕ∞) B → HasCompactSupport B →
      ∀ (Cp : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)), IsCompact Cp →
        (∀ p ∈ tsupport B, ∃ q ∈ Cp,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) →
        ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) ∧
        HasCompactSupport (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) ∧
        ∀ p ∈ tsupport (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]),
          ∃ q ∈ (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (q.1, q.2 * q.1)) '' Cp,
            p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                  InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units.solution
