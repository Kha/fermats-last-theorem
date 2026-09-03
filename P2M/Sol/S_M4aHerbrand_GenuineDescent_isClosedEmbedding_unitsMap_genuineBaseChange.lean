import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
namespace P2MW.S_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange

set_option autoImplicit false

open NumberField

namespace K42IE

open NumberField TensorProduct Topology M4aHerbrand.Bridge

theorem isClosedEmbedding_genuineβ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : IsClosedEmbedding (genuineβ K L) := by
  letI alg : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (genuineβ K L).toAlgebra
  have hβ : Continuous (algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)) := continuous_genuineβ K L
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L hβ (genuineTensorEquiv K L)

  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hℓ1 : ℓ 1 = 1 := by
    have h := congrArg (fun f : K →ₗ[K] K => f 1) hℓ
    simpa using h

  let r : AdeleRing (𝓞 L) L →ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 K) K :=
    (TensorProduct.AlgebraTensorModule.rid K (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K)).toLinearMap ∘ₗ
      (ℓ.baseChange (AdeleRing (𝓞 K) K)) ∘ₗ (genuineTensorEquiv K L).symm.toLinearEquiv.toLinearMap
  have hsymm : ∀ a : AdeleRing (𝓞 K) K, (genuineTensorEquiv K L).symm (genuineβ K L a) = a ⊗ₜ[K] (1 : L) := by
    intro a
    rw [AlgEquiv.symm_apply_eq]
    exact (genuineTensorEquiv_tmul_one K L a).symm
  have hr : Function.LeftInverse r (genuineβ K L) := by
    intro a
    change (TensorProduct.AlgebraTensorModule.rid K (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K))
      (ℓ.baseChange (AdeleRing (𝓞 K) K) ((genuineTensorEquiv K L).symm (genuineβ K L a))) = a
    rw [hsymm, LinearMap.baseChange_tmul, hℓ1, TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  exact hr.isClosedEmbedding hrc (continuous_genuineβ K L)

end K42IE

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Topology.IsClosedEmbedding
      (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom :
        (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) := by
  exact (K42IE.isClosedEmbedding_genuineβ K L).units_map
