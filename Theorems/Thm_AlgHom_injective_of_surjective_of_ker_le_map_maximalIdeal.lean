import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import P2M.Util
import P2M.Sol.S_AlgHom_injective_of_surjective_of_ker_le_map_maximalIdeal

universe u v w x
theorem AlgHom.injective_of_surjective_of_ker_le_map_maximalIdeal
    {𝒪 : Type u} {A : Type v} {B : Type w} [CommRing 𝒪] [IsLocalRing 𝒪]
    [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A] [IsLocalHom (algebraMap 𝒪 A)]
    [CommRing B] [Algebra 𝒪 B] [Module.Free 𝒪 B]
    (f : A →ₐ[𝒪] B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    Function.Injective f := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_injective_of_surjective_of_ker_le_map_maximalIdeal.solution
