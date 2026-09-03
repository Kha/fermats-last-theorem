import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import P2M.Util
import P2M.Sol.S_LinearMap_finrank_ker_baseChange_le_padicValInt_det
set_option autoImplicit false

theorem LinearMap.finrank_ker_baseChange_le_padicValInt_det
    {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (A : L →ₗ[ℤ] L) (hA : LinearMap.det A ≠ 0) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [CharP F p] :
    Module.finrank F ↥(LinearMap.ker (A.baseChange F)) ≤ padicValInt p (LinearMap.det A) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_finrank_ker_baseChange_le_padicValInt_det.solution
