import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_ExtCitation_tame_or_descent_of_isSimple
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
open ExtCitation
theorem ExtCitation.tame_or_descent_of_isSimple
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p) {k : Type} [Field k] [Finite k] [CharP k p]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (N : Rep k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n)
    [FiniteDimensional k N] (hN : Module.finrank k N ≠ 0)
    (hsimple : ∀ W : Submodule k N, (∀ (s : S) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    (∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
        (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
          F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
        (S₀.subgroupOf S).Normal ∧
        (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ cycloChar p (primeLocalToGlobal q s) = 1) ∧
        ¬ p ∣ (S₀.subgroupOf S).index) ∨
    (∃ (S' : Subgroup (primeLocalGaloisGroup q)) (hle : S' ≤ S),
        (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
          F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S') ∧
        (S'.subgroupOf S).Normal ∧ (S'.subgroupOf S).index = p ∧
        Nat.card (MonoidHom.mrange (N.ρ.comp (Subgroup.inclusion hle)))
          < Nat.card (MonoidHom.mrange N.ρ)) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_tame_or_descent_of_isSimple.solution
