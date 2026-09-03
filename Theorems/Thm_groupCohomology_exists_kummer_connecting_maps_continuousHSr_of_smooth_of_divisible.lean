import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem groupCohomology.exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (E : Rep.{0} ℤ G)
    (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (hdiv : ∀ x : E, ∃ y : E, (p : ℤ) • y = x) :
    ∃ (δ : ↥(continuousH1Sr r S E) →+ continuousH2Sr r S (repTorsionP p E))
      (ι : continuousH2Sr r S (repTorsionP p E) →+ continuousH2Sr r S E),
      (∀ x : ↥(continuousH1Sr r S E), δ x = 0 ↔ ∃ y : ↥(continuousH1Sr r S E), x = p • y) ∧
      (∀ v : continuousH2Sr r S (repTorsionP p E), ι v = 0 ↔ ∃ x, δ x = v) ∧
      (∀ w : continuousH2Sr r S E, (∃ v, ι v = w) ↔ p • w = 0) ∧
      (∀ z : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
        ∃ hz : (fun x : G × G => ((z : G × G → repTorsionP p E) x).1) ∈ levelCocyclesSr₂ r S E,
          ι (continuousH2Srπ r S (repTorsionP p E) z) = continuousH2Srπ r S E ⟨_, hz⟩) ∧
      (∀ (c : ↥(levelCocyclesSr₁ r S E)) (b : G → E), IsLevelConstantSr₁ r S b → (∀ g, p • b g = (c.1 : G → E) g) →
        ∃ w : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
          (∀ x : G × G, ((w : G × G → repTorsionP p E) x).1 = (d₁₂ E).hom b x) ∧
          δ ⟨(H1π E).hom c.1, H1π_mem_continuousH1Sr r S E c.2⟩ = continuousH2Srπ r S (repTorsionP p E) w) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.solution
