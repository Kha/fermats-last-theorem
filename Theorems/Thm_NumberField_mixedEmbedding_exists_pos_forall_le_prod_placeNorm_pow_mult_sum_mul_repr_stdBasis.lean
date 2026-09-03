import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis

open scoped NumberField nonZeroDivisors
open scoped Classical in

theorem NumberField.mixedEmbedding.exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis
    {F : Type} [Field F] [NumberField F] (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    let L : (Module.Free.ChooseBasisIndex ℤ I → ℤ) → index F → ℝ := fun m i =>
      ∑ j, (m j : ℝ) * (fractionalIdealLatticeBasis F I).repr (stdBasis F i) j
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ m : Module.Free.ChooseBasisIndex ℤ I → ℤ, m ≠ 0 →
      δ₀ ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, |L m (Sum.inl w)| ^ w.1.mult)
           * ∏ w : {w : InfinitePlace F // w.IsComplex},
             Real.sqrt ((L m (Sum.inr (w, 0)))^2 + (L m (Sum.inr (w, 1)))^2) ^ w.1.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis.solution
