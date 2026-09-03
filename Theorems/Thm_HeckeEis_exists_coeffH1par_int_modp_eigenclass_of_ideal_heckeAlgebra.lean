import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra
    (N : ℕ) [NeZero N] (n : ℕ) (S : Set ℕ) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpN : ¬ p ∣ N) (hn : n < p) (Q : ℕ → Prop) (a : ℕ → ℤ)
    (𝔪 : Ideal (CuspForm.heckeAlgebra N ((n : ℤ) + 2) S)) (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : (p : CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) ∈ 𝔪)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), Q ℓ →
      CuspForm.heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) ∈ 𝔪) :
    ∃ y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      (¬ ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), y = (p : ℤ) • y') ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N → Q ℓ →
        ∀ T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℤ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
          ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), T y - (a ℓ : ℤ) • y = (p : ℤ) • y' := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra.solution
