import Mathlib
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import P2M.Util
import P2M.Sol.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one

set_option autoImplicit false

universe u

open TensorProduct

theorem CoherentBaseChange.TwoTermComplex.exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
    (𝔭 : PrimeSpectrum R) (h𝔭 : G.fibreH0 𝔭 ≤ 1) :
    ∃ (h : R) (J : Ideal R), h ∉ 𝔭.asIdeal ∧
      ∀ (B : Type u) [CommRing B] [Algebra R B], IsUnit (algebraMap R B h) →
        Nonempty (G.H0 B ≃ₗ[B] (J.map (algebraMap R B)).annihilator) := by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.solution
