import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import P2M.Util
import P2M.Sol.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed

theorem AlgHom.exists_algEquiv_comp_eq_of_isAlgClosed
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {M : Type*} [Field M] [Algebra K M] (σ τ : M →ₐ[K] Ω) :
    ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed.solution
