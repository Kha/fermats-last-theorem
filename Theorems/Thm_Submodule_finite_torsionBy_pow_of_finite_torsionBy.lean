import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_finite_torsionBy_pow_of_finite_torsionBy

theorem Submodule.finite_torsionBy_pow_of_finite_torsionBy
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)
    (h : Finite (Submodule.torsionBy R M a)) (k : ℕ) :
    Finite (Submodule.torsionBy R M (a ^ k)) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_finite_torsionBy_pow_of_finite_torsionBy.solution
