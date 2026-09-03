import Mathlib.NumberTheory.Height.NumberField
import P2M.Util
import P2M.Sol.S_Height_logHeight_algebraMap

theorem Height.logHeight_algebraMap {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    logHeight (fun i => algebraMap K L (x i))
      = (Module.finrank K L : ℝ) * logHeight x := by p2m_exact_reverting @_root_.P2MW.S_Height_logHeight_algebraMap.solution
