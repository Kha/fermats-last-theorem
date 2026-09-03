import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_les_continuousHS_of_shortExact_of_isLevelConstant
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (N1 N2 N3 : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) N1] [FiniteDimensional (ZMod p) N2] [FiniteDimensional (ZMod p) N3]
    (f : N1 ⟶ N2) (g : N2 ⟶ N3) (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).ShortExact)
    (hsm : ∀ m : N2, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N2.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N2.ρ s = 1) :
    ∃ (i₀ : N1.ρ.invariants →ₗ[ZMod p] N2.ρ.invariants) (p₀ : N2.ρ.invariants →ₗ[ZMod p] N3.ρ.invariants)
      (δ₀ : N3.ρ.invariants →ₗ[ZMod p] ↥(continuousH1S S N1))
      (i₁ : ↥(continuousH1S S N1) →ₗ[ZMod p] ↥(continuousH1S S N2))
      (p₁ : ↥(continuousH1S S N2) →ₗ[ZMod p] ↥(continuousH1S S N3))
      (δ₁ : ↥(continuousH1S S N3) →ₗ[ZMod p] continuousH2S S N1)
      (i₂ : continuousH2S S N1 →ₗ[ZMod p] continuousH2S S N2)
      (p₂ : continuousH2S S N2 →ₗ[ZMod p] continuousH2S S N3),

      (∀ x, (i₀ x : N2) = f.hom x) ∧ (∀ y, (p₀ y : N3) = g.hom y) ∧
      (∀ x, (i₁ x : H1 N2) = (map (MonoidHom.id _) f 1).hom x) ∧
      (∀ y, (p₁ y : H1 N3) = (map (MonoidHom.id _) g 1).hom y) ∧

      (∀ (x : N3.ρ.invariants) (y : N2) (c : cocycles₁ N1), g.hom y = (x : N3) →
          (∀ s, f.hom (c s) = N2.ρ s y - y) → (δ₀ x : H1 N1) = (H1π N1).hom c) ∧

      (∀ (z : levelCocyclesS₂ S N1) (z' : levelCocyclesS₂ S N2),
          (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st = f.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1) st)) → i₂ (continuousH2Sπ S N1 z) = continuousH2Sπ S N2 z') ∧
      (∀ (z : levelCocyclesS₂ S N2) (z' : levelCocyclesS₂ S N3),
          (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) st = g.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st)) → p₂ (continuousH2Sπ S N2 z) = continuousH2Sπ S N3 z') ∧

      (∀ (x : ↥(continuousH1S S N3)) (c : cocycles₁ N3) (b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) (e : levelCocyclesS₂ S N1),
          (H1π N3).hom c = (x : H1 N3) → (∀ s, g.hom (b s) = c s) → IsLevelConstantS₁ S b →
          (∀ s t, f.hom ((e : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1) (s, t)) = N2.ρ s (b t) - b (s * t) + b s) →
          δ₁ x = continuousH2Sπ S N1 e) ∧

      Function.Injective i₀ ∧ Function.Exact i₀ p₀ ∧ Function.Exact p₀ δ₀ ∧ Function.Exact δ₀ i₁ ∧
      Function.Exact i₁ p₁ ∧ Function.Exact p₁ δ₁ ∧ Function.Exact δ₁ i₂ ∧ Function.Exact i₂ p₂ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant.solution
