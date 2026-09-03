import Mathlib
import Definitions.Def_CohCarrier_Inst
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL

set_option autoImplicit false

open scoped TensorProduct

theorem CohCarrier.exists_injective_linearMap_baseChange_H1_heckeTL
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] :
    ∃ j : K ⊗[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[K] CohCarrier.H1 M H K,
      Function.Injective j ∧
      (∀ (c : K) (w : CohCarrier.H1 M H 𝒪),
        j (c ⊗ₜ[𝒪] w) = c • ((algebraMap 𝒪 K).toAddMonoidHom.comp w)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (x : K ⊗[𝒪] CohCarrier.H1 M H 𝒪),
        j (((CohCarrier.heckeTL M H 𝒪 ℓ).baseChange K) x) =
          CohCarrier.heckeTL M H K ℓ (j x) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL.solution
