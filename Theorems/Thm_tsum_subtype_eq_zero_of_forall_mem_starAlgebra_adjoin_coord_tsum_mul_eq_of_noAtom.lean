import Mathlib
import P2M.Util
import P2M.Sol.S_tsum_subtype_eq_zero_of_forall_mem_starAlgebra_adjoin_coord_tsum_mul_eq_of_noAtom

set_option autoImplicit false

open scoped ComplexConjugate

theorem tsum_subtype_eq_zero_of_forall_mem_starAlgebra_adjoin_coord_tsum_mul_eq_of_noAtom
    {ι : Type*} (X : Set (ι → ℂ × ℂ)) (hX : IsCompact X)
    (a : ℕ → ℂ) (ha : Summable fun i => ‖a i‖) (x : ℕ → X)
    (Λ : C(X, ℂ) →L[ℂ] ℂ) (F : Finset ι) (τ : ι → ℂ × ℂ)
    (hcyl : ∀ ε > (0 : ℝ), ∃ U : ι → Set (ℂ × ℂ), (∀ k ∈ F, IsOpen (U k) ∧ τ k ∈ U k) ∧
      ∀ g : C(X, ℂ), (∀ y : X, (∃ k ∈ F, (y : ι → ℂ × ℂ) k ∉ U k) → g y = 0) →
        (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε)
    (hid : ∀ g ∈ StarAlgebra.adjoin ℂ
        ((Set.range fun k : F => (⟨fun y : X => ((y : ι → ℂ × ℂ) k).1,
            ((continuous_apply (k : ι)).comp continuous_subtype_val).fst⟩ : C(X, ℂ))) ∪
          Set.range fun k : F => (⟨fun y : X => ((y : ι → ℂ × ℂ) k).2,
            ((continuous_apply (k : ι)).comp continuous_subtype_val).snd⟩ : C(X, ℂ))),
      ∑' i, a i * g (x i) = Λ g) :
    ∑' i : {i : ℕ // ∀ k ∈ F, ((x i : X) : ι → ℂ × ℂ) k = τ k}, a i = 0 := by p2m_exact_reverting @_root_.P2MW.S_tsum_subtype_eq_zero_of_forall_mem_starAlgebra_adjoin_coord_tsum_mul_eq_of_noAtom.solution
