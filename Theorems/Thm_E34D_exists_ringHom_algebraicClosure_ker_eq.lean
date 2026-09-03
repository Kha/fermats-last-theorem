import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod
import P2M.Util
import P2M.Sol.S_E34D_exists_ringHom_algebraicClosure_ker_eq
set_option autoImplicit false

theorem E34D.exists_ringHom_algebraicClosure_ker_eq {R : Type*} [CommRing R] {p : ℕ}
    [hp : Fact p.Prime] [Module.Finite ℤ R]
    {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
    ∃ φ : R →+* AlgebraicClosure (ZMod p), RingHom.ker φ = 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_E34D_exists_ringHom_algebraicClosure_ker_eq.solution
