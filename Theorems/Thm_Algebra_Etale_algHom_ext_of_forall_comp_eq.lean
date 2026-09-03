import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import P2M.Util
import P2M.Sol.S_Algebra_Etale_algHom_ext_of_forall_comp_eq

theorem Algebra.Etale.algHom_ext_of_forall_comp_eq
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    {B : Type*} [Semiring B] [Algebra K B]
    {C : Type*} [CommRing C] [Algebra K C] [Algebra.Etale K C]
    {ψ₁ ψ₂ : B →ₐ[K] C} (h : ∀ χ : C →ₐ[K] Ω, χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_algHom_ext_of_forall_comp_eq.solution
