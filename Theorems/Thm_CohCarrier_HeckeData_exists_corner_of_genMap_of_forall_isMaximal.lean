import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_exists_corner_of_genMap_of_forall_isMaximal

set_option autoImplicit false

open IsLocalRing IharaLemma

open scoped IsMulCommutative in

theorem CohCarrier.HeckeData.exists_corner_of_genMap_of_forall_isMaximal
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    (D D' : CohCarrier.HeckeData 𝒪 V (ResidueField 𝒪))
    (φ : D.Gen → D'.Gen) (hop : ∀ g, D'.op (φ g) = D.op g)
    (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i : Fin Sp.n)
    (πk : Sp.CornerRing i →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g)
    (hnew : ∀ 𝔪' : Ideal ↥D'.opSubalgebra, 𝔪'.IsMaximal →
      (∀ (g : D.Gen) (c : 𝒪), IsLocalRing.residue 𝒪 c = D.θbar g →
        ((⟨D'.op (φ g), Algebra.subset_adjoin (Set.mem_range_self (φ g))⟩ : ↥D'.opSubalgebra)
          - algebraMap 𝒪 ↥D'.opSubalgebra c) ∈ 𝔪') →
      ∀ g' : D'.Gen, ∃ c' : 𝒪, IsLocalRing.residue 𝒪 c' = D'.θbar g' ∧
        ((⟨D'.op g', Algebra.subset_adjoin (Set.mem_range_self g')⟩ : ↥D'.opSubalgebra)
          - algebraMap 𝒪 ↥D'.opSubalgebra c') ∈ 𝔪') :
    ∃ (Sp' : IharaLemma.IdempotentSplitting ↥D'.opSubalgebra) (i' : Fin Sp'.n)
      (πk' : Sp'.CornerRing i' →ₐ[𝒪] ResidueField 𝒪),
      (∀ g' : D'.Gen, πk' (Sp'.toCornerRing i'
        ⟨D'.op g', Algebra.subset_adjoin (Set.mem_range_self g')⟩) = D'.θbar g') ∧
      (∀ v : V, v ∈ IharaLemma.cornerSubmodule (M := V) (Sp.e i) ↔
        v ∈ IharaLemma.cornerSubmodule (M := V) (Sp'.e i')) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_exists_corner_of_genMap_of_forall_isMaximal.solution
