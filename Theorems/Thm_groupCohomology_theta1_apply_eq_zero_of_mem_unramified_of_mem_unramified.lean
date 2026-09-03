import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousDuality
import P2M.Util
import P2M.Sol.S_groupCohomology_theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified
attribute [-instance] AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] groupCohomology.locTotal₂S_apply groupCohomology.locTotal_apply groupCohomology.totalPairing_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q)
      (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (θ₁ : continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))))
    (hθ₁ : IsTheta1 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M :
        Rep.res (primeLocalToGlobal q) M →ₗ[ZMod p] Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
          ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
      inv θ₁)
    (Lur : Submodule (ZMod p) (H1 (Rep.res (primeLocalToGlobal q) M)))
    (hLur : ∀ x : H1 (Rep.res (primeLocalToGlobal q) M), x ∈ Lur ↔
      ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal q) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, primeLocalToGlobal q s ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (primeLocalToGlobal q) M).ρ s m - m) ∧
        H1π _ c = x)
    (L'ur : Submodule (ZMod p) (H1 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))))
    (hL'ur : ∀ x : H1 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))), x ∈ L'ur ↔
      ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, primeLocalToGlobal q s ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ →
            c.val s = (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x)
    (x : continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) (hx : (x : H1 (Rep.res (primeLocalToGlobal q) M)) ∈ Lur)
    (y : continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))))
    (hy : (y : H1 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))) ∈ L'ur) :
    θ₁ x y = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified.solution
