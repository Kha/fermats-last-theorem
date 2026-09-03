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
import P2M.Sol.S_AlgHom_length_quotient_congruenceIdeal_le_length_cotangent

universe u v w x
theorem AlgHom.length_quotient_congruenceIdeal_le_length_cotangent
    {𝒪 : Type u} {R : Type v} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hfg : (RingHom.ker πR).FG) :
    Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ≤
      Module.length 𝒪 (RingHom.ker πR).Cotangent := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_length_quotient_congruenceIdeal_le_length_cotangent.solution
