import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import P2M.Util
import P2M.Sol.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective

universe u

open scoped TensorProduct

theorem TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
      (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.solution
