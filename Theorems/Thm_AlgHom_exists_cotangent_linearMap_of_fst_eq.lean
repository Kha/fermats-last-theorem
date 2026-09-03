import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.TrivSqZeroExt.Basic
import P2M.Util
import P2M.Sol.S_AlgHom_exists_cotangent_linearMap_of_fst_eq

universe u v x
theorem AlgHom.exists_cotangent_linearMap_of_fst_eq
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N) (hψ : ∀ r : R, (ψ r).fst = πR r) :
    ∃ f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N,
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_cotangent_linearMap_of_fst_eq.solution
