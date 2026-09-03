import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import P2M.Util
import P2M.Sol.S_Algebra_Etale_eq_of_forall_algHom_apply_eq

theorem Algebra.Etale.eq_of_forall_algHom_apply_eq
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    {B : Type*} [CommRing B] [Algebra K B] [Algebra.Etale K B]
    {x y : B} (h : ∀ χ : B →ₐ[K] Ω, χ x = χ y) : x = y := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_eq_of_forall_algHom_apply_eq.solution
