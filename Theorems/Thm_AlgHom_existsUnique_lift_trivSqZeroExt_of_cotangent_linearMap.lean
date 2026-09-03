import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.TrivSqZeroExt.Basic
import P2M.Util
import P2M.Sol.S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap

universe u v x
theorem AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N) :
    ∃! ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N, (∀ r : R, (ψ r).fst = πR r) ∧
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap.solution
