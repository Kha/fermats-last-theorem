import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import P2M.Util
import P2M.Sol.S_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain

theorem AlgHom.exists_eq_comp_evalAlgHom_of_isDomain
    {K : Type*} [Field K] {Ω : Type*} [CommRing Ω] [Algebra K Ω] [IsDomain Ω]
    {J : Type*} [_root_.Finite J] {A : J → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    (φ : (Π j, A j) →ₐ[K] Ω) :
    ∃ (j : J) (φ₀ : A j →ₐ[K] Ω), φ = φ₀.comp (Pi.evalAlgHom K A j) := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain.solution
