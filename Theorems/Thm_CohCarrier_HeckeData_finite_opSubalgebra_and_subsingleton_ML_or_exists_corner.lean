import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner

set_option autoImplicit false

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg
open scoped IsMulCommutative in

theorem CohCarrier.HeckeData.finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : CohCarrier.HeckeData 𝒪 V k) :
    Module.Finite 𝒪 ↥D.opSubalgebra ∧
      (Subsingleton D.ML ∨
        ∃ (S : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i : Fin S.n)
          (r : S.CornerRing i →+* k),
          Function.Surjective r ∧
            (∀ c : 𝒪, r (algebraMap 𝒪 (S.CornerRing i) c) = algebraMap 𝒪 k c) ∧
            (∀ g : D.Gen,
              r (S.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩)
                = D.θbar g) ∧
            ∃ e : D.ML ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
              ∀ (g : D.Gen) (m : D.ML),
                e ((MvPolynomial.X g : D.FreeAlg) • m)
                  = S.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
                      • e m) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner.solution
