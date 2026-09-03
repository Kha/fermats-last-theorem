import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import P2M.Util
import P2M.Sol.S_Algebra_Etale_existsUnique_algHom_forall_comp_eq_of_equivariant

theorem Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃! ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_existsUnique_algHom_forall_comp_eq_of_equivariant.solution
