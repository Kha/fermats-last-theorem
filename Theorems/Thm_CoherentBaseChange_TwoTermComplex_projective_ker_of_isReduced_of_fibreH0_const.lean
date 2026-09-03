import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Nilpotent.Defs
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import P2M.Util
import P2M.Sol.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const

universe u v w

open scoped TensorProduct
open CoherentBaseChange

theorem CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_of_fibreH0_const
    {R : Type u} [CommRing R] [IsReduced R] (G : TwoTermComplex.{u, v} R) {c : ℕ}
    (h0 : ∀ 𝔭 : PrimeSpectrum R, G.fibreH0 𝔭 = c) :
    Module.Projective R (LinearMap.ker G.d) ∧
      (∀ (A : Type w) [CommRing A] [Algebra R A], Function.Bijective (G.kerBaseChangeHom A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
        (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker G.d) = c := by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.solution
