import Mathlib
import P2M.Util
import P2M.Sol.S_isSMulRegular_iff_of_free

theorem isSMulRegular_iff_of_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {r : R} :
    IsSMulRegular M r ↔ IsSMulRegular R r := by p2m_exact_reverting @_root_.P2MW.S_isSMulRegular_iff_of_free.solution
