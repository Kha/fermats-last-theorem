import Mathlib
import P2M.Util
import P2M.Sol.S_Height_mulHeightBound_map_le

theorem Height.mulHeightBound_map_le {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {ι ι' : Type*} [Finite ι] [Finite ι'] (p : ι' → MvPolynomial ι K) :
    Height.mulHeightBound (fun j => MvPolynomial.map (algebraMap K L) (p j))
      ≤ Height.mulHeightBound p ^ Module.finrank K L := by p2m_exact_reverting @_root_.P2MW.S_Height_mulHeightBound_map_le.solution
