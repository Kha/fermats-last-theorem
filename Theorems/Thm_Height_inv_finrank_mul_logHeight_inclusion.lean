import Mathlib.NumberTheory.Height.NumberField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import P2M.Util
import P2M.Sol.S_Height_inv_finrank_mul_logHeight_inclusion

theorem Height.inv_finrank_mul_logHeight_inclusion
    {K L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥K] [NumberField ↥L]
    (h : K ≤ L) {ι : Type*} [Finite ι] (x : ι → ↥K) :
    (Module.finrank ℚ ↥L : ℝ)⁻¹ * logHeight (fun i => IntermediateField.inclusion h (x i))
      = (Module.finrank ℚ ↥K : ℝ)⁻¹ * logHeight x := by p2m_exact_reverting @_root_.P2MW.S_Height_inv_finrank_mul_logHeight_inclusion.solution
