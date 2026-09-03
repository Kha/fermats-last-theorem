import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import P2M.Util
import P2M.Sol.S_Rep_finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem Rep.finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] (Λ : Subgroup Γ) [Λ.Normal] [Finite (Γ ⧸ Λ)]
    (hcop : (Nat.card (Γ ⧸ Λ)).Coprime p)
    (X : ShortComplex (Rep.{0} (ZMod p) Γ)) (hX : X.ShortExact) [FiniteDimensional (ZMod p) X.X₂]
    (h₂ : ∀ s ∈ Λ, X.X₂.ρ s = 1)
    (N : Rep.{0} (ZMod p) Γ) [FiniteDimensional (ZMod p) N] :
    Module.finrank (ZMod p) (X.X₂ ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants =
      Module.finrank (ZMod p) (X.X₁ ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants +
      Module.finrank (ZMod p) (X.X₃ ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime.solution
