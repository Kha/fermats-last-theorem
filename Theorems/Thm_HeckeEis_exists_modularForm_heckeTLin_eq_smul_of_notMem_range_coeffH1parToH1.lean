import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
attribute [-simp] HeckeEis.coe_linePow

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
    (N : ℕ) [NeZero N] (n : ℕ) (S₀ : Set ℕ) (Λ : ℕ → ℂ)
    (x : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : x ∉ LinearMap.range (HeckeEis.coeffH1parToH1
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∃ T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          →ₗ[ℂ] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         HeckeEis.IsCoeffHeckeOnH1 N ℓ
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) T) ∧
        T x - Λ ℓ • x ∈ LinearMap.range (HeckeEis.coeffH1parToH1
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), f ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1.solution
