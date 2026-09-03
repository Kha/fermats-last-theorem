import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier
open scoped TensorProduct

theorem CohCarrier.HeckeData.exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    (D : HeckeData 𝒪 V k)

    (Z : Module.End 𝒪 V) (hZ : ∀ g : D.Gen, Z * D.op g = D.op g * Z) (z₀ : D.FreeAlg)

    (K : Type) [Field K] [IsAlgClosed K] [Algebra 𝒪 K] [Algebra k K] [IsScalarTower 𝒪 k K]

    (htest : ∀ (x : K ⊗[𝒪] V) (b : K), x ≠ 0 →
      (∀ g : D.Gen, (D.op g).baseChange K x = algebraMap k K (D.θbar g) • x) →
      Z.baseChange K x = b • x → b = algebraMap k K (D.thetaTilde z₀)) :
    ∃ n : ℕ, ∀ v : V,
      D.toML (((Z - D.opAlgHom z₀) ^ n) v) ∈
        (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector.solution
