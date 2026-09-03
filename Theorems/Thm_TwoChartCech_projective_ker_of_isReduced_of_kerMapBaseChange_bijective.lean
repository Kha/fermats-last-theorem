import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Nilpotent.Defs
import P2M.Util
import P2M.Sol.S_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective

universe u

open scoped TensorProduct

theorem TwoChartCech.projective_ker_of_isReduced_of_kerMapBaseChange_bijective
    {R : Type u} [CommRing R] [IsReduced R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1] {d : C0 →ₗ[R] C1}
    (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d)
    (hG : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A))
    {n : ℕ} (hH0 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Projective R (LinearMap.ker d) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], Function.Bijective (TwoChartCech.kerBaseChangeHom d A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
          (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker d) = n := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective.solution
