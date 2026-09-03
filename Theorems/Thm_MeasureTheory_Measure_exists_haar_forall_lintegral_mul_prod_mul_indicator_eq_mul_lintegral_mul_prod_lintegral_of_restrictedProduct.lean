import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.Measure.exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct
    {B α κ : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [T2Space B]
    [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    [Fintype α] {A : α → Type*} [∀ a, Group (A a)] [∀ a, TopologicalSpace (A a)]
    [∀ a, IsTopologicalGroup (A a)] [∀ a, LocallyCompactSpace (A a)] [∀ a, T2Space (A a)]
    [∀ a, SecondCountableTopology (A a)] [∀ a, MeasurableSpace (A a)] [∀ a, BorelSpace (A a)]
    {G : κ → Type*} [∀ k, Group (G k)] [∀ k, TopologicalSpace (G k)] [∀ k, IsTopologicalGroup (G k)]
    [∀ k, LocallyCompactSpace (G k)] [∀ k, T2Space (G k)] [∀ k, SecondCountableTopology (G k)]
    [∀ k, MeasurableSpace (G k)] [∀ k, BorelSpace (G k)]
    (q : ∀ a, B →* A a) (hq : ∀ a, Continuous (q a)) (p : ∀ k, B →* G k) (hp : ∀ k, Continuous (p k))
    (U : ∀ k, Subgroup (G k)) (hUc : ∀ k, IsCompact (U k : Set (G k))) (hUo : ∀ k, IsOpen (U k : Set (G k)))
    (hP : ∀ Sf : Finset κ, IsOpen {b : B | ∀ k ∉ Sf, p k b ∈ U k})
    (hsurj : ∀ (Sf : Finset κ) (y : ∀ a, A a) (x : ∀ k, G k), (∀ k ∉ Sf, x k ∈ U k) →
      ∃ b : B, (∀ a, q a b = y a) ∧ ∀ k, p k b = x k)
    (hbox : ∀ (D : ∀ a, Set (A a)) (C : ∀ k, Set (G k)), (∀ a, IsCompact (D a)) → (∀ k, IsCompact (C k)) →
      {k | C k ≠ (U k : Set (G k))}.Finite → IsCompact {b : B | (∀ a, q a b ∈ D a) ∧ ∀ k, p k b ∈ C k})
    (ν : Measure B) [ν.IsHaarMeasure] :
    ∃ (νA : Measure (∀ a, A a)) (νG : ∀ k, Measure (G k)),
      νA.IsHaarMeasure ∧ (∀ k, (νG k).IsHaarMeasure ∧ νG k (U k : Set (G k)) = 1) ∧
      ∀ (Sf : Finset κ) (g : (∀ a, A a) → ℝ≥0∞) (f : ∀ k, G k → ℝ≥0∞),
        Measurable g → (∀ k ∈ Sf, Measurable (f k)) →
        ∫⁻ b, g (fun a => q a b) * (∏ k ∈ Sf, f k (p k b)) *
            Set.indicator {b : B | ∀ k, k ∉ Sf → p k b ∈ U k} (fun _ => (1 : ℝ≥0∞)) b ∂ν =
          (∫⁻ y, g y ∂νA) * ∏ k ∈ Sf, ∫⁻ x, f k x ∂(νG k) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct.solution
