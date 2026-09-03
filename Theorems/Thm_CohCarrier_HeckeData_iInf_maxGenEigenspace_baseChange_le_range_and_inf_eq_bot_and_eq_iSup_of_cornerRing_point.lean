import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point

set_option autoImplicit false

open Polynomial IsLocalRing
open scoped TensorProduct IsMulCommutative

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem CohCarrier.HeckeData.iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {H : Type} [AddCommGroup H] [Module 𝒪 H] [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
    (D : CohCarrier.HeckeData 𝒪 H (ResidueField 𝒪))
    (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i₀ : Fin Sp.n)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i₀
      ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g)
    (F : Type) [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F)) :

    (∀ a : D.Gen → F,
      (∀ g : D.Gen, (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)) →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ≤
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F)) ∧

    (∀ a : D.Gen → F,
      (∃ g : D.Gen, ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)) →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) = ⊥) ∧

    (IsAlgClosed F →
      LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) =
        ⨆ (a : D.Gen → F) (_ : ∀ g : D.Gen, (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)),
          ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.solution
