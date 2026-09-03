import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two
attribute [-simp] HeckeEis.coe_linePow

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two
    (N : ℕ) [NeZero N] (n : ℕ) (S : Set ℕ) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpN : ¬ p ∣ N) (hn : n < p) (Q : ℕ → Prop) (a : ℕ → ℤ)
    (𝔪 : Ideal (CuspForm.heckeAlgebra N ((n : ℤ) + 2) S)) (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : (p : CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) ∈ 𝔪)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), Q ℓ →
      CuspForm.heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) ∈ 𝔪)
    (K : Type*) [Field K] [CharP K p] :
    ∃ x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype), x ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N → Q ℓ →
        ∃ T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[K] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj K n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
          T x = ((a ℓ : ℤ) : K) • x := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two.solution
