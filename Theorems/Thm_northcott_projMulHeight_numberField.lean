import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.Order.Northcott
import P2M.Util
import P2M.Sol.S_northcott_projMulHeight_numberField

theorem northcott_projMulHeight_numberField (K : Type) [Field K] [NumberField K] (ι : Type) [Finite ι] :
    Northcott (Projectivization.mulHeight : Projectivization K (ι → K) → ℝ) := by p2m_exact_reverting @_root_.P2MW.S_northcott_projMulHeight_numberField.solution
