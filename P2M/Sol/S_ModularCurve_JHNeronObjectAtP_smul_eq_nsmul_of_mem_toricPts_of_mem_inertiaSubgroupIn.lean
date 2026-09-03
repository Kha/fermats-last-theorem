import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
namespace P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_nsmul_of_mem_toricPts_of_mem_inertiaSubgroupIn

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (c : ℕ) (hc : ∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) :
    ∀ x ∈ O.toricPts m, σ • x = c • x := by

  have key : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      σ • O.toricPoint m hm χ = c • O.toricPoint m hm χ :=
    fun χ => O.toricLift_inertia m hm σ hσ c hc χ

  intro x hx
  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx
  let f : JH M H →+ JH M H := DistribSMul.toAddMonoidHom (JH M H) σ
  let g : JH M H →+ JH M H := nsmulAddMonoidHom c
  have hle : AddSubgroup.closure (Set.range (O.toricPoint m hm)) ≤ f.eqLocus g :=
    (AddSubgroup.closure_le _).mpr (by
      rintro _ ⟨χ, rfl⟩
      exact key χ)
  exact hle hx
