import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_TwoChartCech_Mumford_projective_ker_of_fibre_surjective
attribute [-simp] TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply

universe u

open scoped TensorProduct

theorem TwoChartCech.Mumford.projective_ker_of_fibre_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {C0 C1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
    [Module.Flat A C0] [Module.Flat A C1] (d : C0 →ₗ[A] C1)
    [Module.Finite A (LinearMap.ker d)] [Module.Finite A (C1 ⧸ LinearMap.range d)]
    (hH1 : ∀ (K : Type u) [Field K] [Algebra A K], Function.Surjective (d.baseChange K)) :
    Module.Projective A (LinearMap.ker d) ∧
      (∀ (A' : Type u) [CommRing A'] [Algebra A A'], Function.Bijective (TwoChartCech.kerBaseChangeHom d A')) ∧
      ∀ (K : Type u) [Field K] [Algebra A K],
        Module.finrank K (K ⊗[A] LinearMap.ker d) = Module.finrank K (LinearMap.ker (d.baseChange K)) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Mumford_projective_ker_of_fibre_surjective.solution
