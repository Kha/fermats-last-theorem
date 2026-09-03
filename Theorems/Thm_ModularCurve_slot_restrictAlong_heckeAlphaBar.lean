import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_slot_restrictAlong_heckeAlphaBar
attribute [-simp] ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve

theorem ModularCurve.slot_restrictAlong_heckeAlphaBar (K : Type*) [Field K] [Algebra ℚ K] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hα : HeckeAlphaBarIntegral K N ℓ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (N * ℓ)) (a b : ℕ) (ha : a ∣ N * ℓ) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull (N * ℓ)) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩ =
        qExpand K (N * ℓ) (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN (N * ℓ)), coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (W : Place K (laurentBaseChange K (modularFunctionFieldFull (N * ℓ)))) (γ : ℤ) (hγ : 0 < γ)
    (hW : ∀ x, W.ord x * γ = (ι x).order) :
    W.ramificationIndexAlong (heckeAlphaBar K N ℓ) * Nat.gcd a ℓ = ℓ ∧
    ∃ (a₀ b₀ : ℕ) (_ : NeZero a₀)
      (ι₀ : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K),
      a₀ * Nat.gcd a ℓ = a ∧
      ι₀ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι₀ ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq)) ∧
      (∀ x, (W.restrictAlong (heckeAlphaBar K N ℓ) hα).ord x * ((a₀ * Nat.gcd a₀ (N / a₀) : ℕ) : ℤ)
          = (ι₀ x).order) ∧
      Nat.gcd a ℓ * b₀ ≡ b [MOD Nat.gcd a₀ (N / a₀)] := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_slot_restrictAlong_heckeAlphaBar.solution
