import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_GroupCohomology_LevelConstantHom
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem groupCohomology.nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {Γ : Type} [Group Γ] (Sg : Subgroup Γ) [Sg.Normal]
    (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : Γ →* (ZMod p)ˣ)
    (C N : Rep.{0} (ZMod p) Γ) [FiniteDimensional (ZMod p) N]
    (e : C ≃ₗ[ZMod p] ↥(levelConstantHom (r.comp Sg.subtype) S (ZMod p) (ZMod p)))
    (he : ∀ (g : Γ) (x : C) (s t : ↥Sg), (g⁻¹ * s * g : Γ) = t →
      (e (C.ρ g x) : ↥Sg → ZMod p) s = ((χ g : (ZMod p)ˣ) : ZMod p) * (e x : ↥Sg → ZMod p) t) :
    Nonempty ((C ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants ≃ₗ[ZMod p] ↥(eqLevelConstantHom r S Sg (N.twist χ))) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom.solution
