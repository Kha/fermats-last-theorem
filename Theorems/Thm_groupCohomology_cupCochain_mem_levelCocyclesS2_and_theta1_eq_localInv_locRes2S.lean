import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import P2M.Util
import P2M.Sol.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ)
    (θ : ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ q))
    (f : cocycles₁ M) (hf : IsLevelConstantS₁ S (⇑f))
    (g : cocycles₁ (M.dualTwist (cycloChar p))) (hg : IsLevelConstantS₁ S (⇑g)) :
    ∃ hc : cupCochain (Module.Dual.eval (ZMod p) M :
          M →ₗ[ZMod p] M.dualTwist (cycloChar p) →ₗ[ZMod p] ofChar (k := ZMod p) (cycloChar p))
        (⇑f) (⇑g) ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)),
      (∀ q : ↥S,
        haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
        ∀ (z : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
          (w : continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))),
          (z : H1 _) = (locRes (extArithLoc S) M (Sum.inr q)).hom ((H1π M).hom f) →
          (w : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom
              ((H1π (M.dualTwist (cycloChar p))).hom g) →
          θ q z w = localInv p ζ (q : Nat.Primes)
            (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q))
              (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, hc⟩))) ∧
      ((locRes (extArithLoc S) M (Sum.inl ())).hom ((H1π M).hom f) = 0 →
        locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inl ()))
          (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, hc⟩) = 0) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S.solution
