import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed

theorem Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    [Module.Finite R A] (S : Subalgebra R A) (k : Type*) [Field k] [IsAlgClosed k] [Algebra R k] (φ : ↥S →ₐ[R] k) :
    ∃ ψ : A →ₐ[R] k, ψ.comp S.val = φ := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed.solution
