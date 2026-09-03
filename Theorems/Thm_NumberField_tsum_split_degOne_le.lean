import Mathlib.NumberTheory.NumberField.DedekindZeta
import Definitions.Def_NumberField_IsSplitPrime
import P2M.Util
import P2M.Sol.S_NumberField_tsum_split_degOne_le
set_option autoImplicit false
namespace NumberField
open scoped NumberField nonZeroDivisors
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]
theorem tsum_split_degOne_le (q : ℕ) (hq : q.Prime) (h3q : 3 ≤ q)
    (hdeg : Module.finrank K M = q) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      ∑' 𝔩 : {I : Ideal (𝓞 K) // IsSplitPrime K M I},
          ((Ideal.absNorm (𝔩 : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹
        ≤ (q : ℝ)⁻¹ * Real.log ‖dedekindZeta M s‖ + C := by p2m_exact_reverting @_root_.P2MW.S_NumberField_tsum_split_degOne_le.solution
