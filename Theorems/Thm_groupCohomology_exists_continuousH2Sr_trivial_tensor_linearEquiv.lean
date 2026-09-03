import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped TensorProduct

theorem groupCohomology.exists_continuousH2Sr_trivial_tensor_linearEquiv
    {k : Type} [Field k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : Rep.{0} k G) :
    ∃ Θ : continuousH2Sr r S (Rep.trivial k G V ⊗ X) ≃ₗ[k] V ⊗[k] continuousH2Sr r S X,
      (∀ (v : V) (z : ↥(levelCocyclesSr₂ r S X)) (w : ↥(levelCocyclesSr₂ r S (Rep.trivial k G V ⊗ X))),
        (∀ st, (w : G × G → (Rep.trivial k G V ⊗ X : Rep.{0} k G)) st = v ⊗ₜ[k] (z : G × G → X) st) →
          Θ (continuousH2Srπ r S (Rep.trivial k G V ⊗ X) w) = v ⊗ₜ[k] continuousH2Srπ r S X z) ∧
      ∀ (φ : V →ₗ[k] V) (ψ : X ⟶ X) (e : (Rep.trivial k G V ⊗ X : Rep.{0} k G) ⟶ (Rep.trivial k G V ⊗ X : Rep.{0} k G)),
        (∀ (v : V) (x : X), e.hom (v ⊗ₜ[k] x) = φ v ⊗ₜ[k] ψ.hom x) →
          Θ.toLinearMap ∘ₗ continuousH2SrMapHom S r e = TensorProduct.map φ (continuousH2SrMapHom S r ψ) ∘ₗ Θ.toLinearMap := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv.solution
