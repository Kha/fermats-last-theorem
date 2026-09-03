import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (κ : Type) [Field κ] [CharP κ p]
    (v : CohCarrier.H1 N ⊥ κ) (hv : v ≠ 0)
    (hpar : v ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ)
    (hdia : ∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v = v)
    (E : Set ℕ) (n : ℕ → ℤ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊥ ℓ κ v = (n ℓ : κ) • v) :
    ∃ φ₀ : CohCarrier.H1 N ⊥ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊥) ℤ ∧
      (¬ ∃ ψ : CohCarrier.H1 N ⊥ ℤ, φ₀ = (p : ℤ) • ψ) ∧
      (∀ σ : CongruenceSubgroup.Gamma0 N, ∃ ψ : CohCarrier.H1 N ⊥ ℤ,
        CohCarrier.diamondRaw N ⊥ ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.heckeT N ⊥ ℓ ℤ φ₀ - (n ℓ) • φ₀ = (p : ℤ) • ψ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul.solution
