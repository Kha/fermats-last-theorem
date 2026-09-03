import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import P2M.Util
import P2M.Sol.S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule

open scoped FourierTransform SchwartzMap
theorem ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : 𝓢(V, ℂ)) (t : V) :
    Summable fun y : LinearMap.BilinForm.dualSubmodule B.flip L =>
      VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule.solution
