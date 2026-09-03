import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem groupCohomology.kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (E : Rep.{0} ℤ G)
    (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (hdiv : ∀ x : E, ∃ y : E, (p : ℤ) • y = x) :
    (∀ c : ↥(levelCocyclesSr₂ r S E), ∃ b : (Fin 2 → G) → E,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g) ∧
      ∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) ∧
    (∀ (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g) →
      (∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) →
      ((∃ e : (Fin 2 → G) → repTorsionP p E,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → e (g * s) = e g) ∧
          ((inhomogeneousCochains E).d 2 3).hom b = ((inhomogeneousCochains E).d 2 3).hom (fun v => ((e v : repTorsionP p E) : E))) ↔
        ∃ y : continuousH2Sr r S E, continuousH2Srπ r S E c = p • y)) ∧
    (∀ u : (Fin 3 → G) → repTorsionP p E,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 3 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → u (g * s) = u g) →
      ((inhomogeneousCochains (repTorsionP p E)).d 3 4).hom u = 0 →
      ((∃ w : (Fin 2 → G) → E,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
          ((inhomogeneousCochains E).d 2 3).hom w = fun t => ((u t : repTorsionP p E) : E)) ↔
        ∃ (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E) (e : (Fin 2 → G) → repTorsionP p E),
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g ∧ e (g * s) = e g) ∧
          (∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) ∧
          (fun t => ((u t : repTorsionP p E) : E)) =
            ((inhomogeneousCochains E).d 2 3).hom b + ((inhomogeneousCochains E).d 2 3).hom (fun v => ((e v : repTorsionP p E) : E)))) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible.solution
