import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite

set_option autoImplicit false

universe u v w

theorem Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    (C : Subalgebra R A) (Ω : Type w) [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
    (h : ↥C →ₐ[R] Ω) : ∃ ν : A →ₐ[R] Ω, ν.comp C.val = h := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite.solution
