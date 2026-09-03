import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (q : Nat.Primes) (hq : (q : ℕ) = p)
    (adm₁ : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔
      ∃ c : cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ (g s : primeLocalGaloisGroup q),
            primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
        ∧ (H1π _).hom c = x) :
    Module.Finite (ZMod p) adm₁ ∧ finrank (ZMod p) adm₁ = 2 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal.solution
