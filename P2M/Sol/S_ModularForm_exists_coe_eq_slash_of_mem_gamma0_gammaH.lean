import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
namespace P2MW.S_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH

set_option autoImplicit false

open scoped MatrixGroups ModularForm Pointwise

theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ F : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by
  set g : GL (Fin 2) ℝ := (γ : GL (Fin 2) ℝ) with hg
  have hslash : ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] g) := ModularForm.SL_slash _ γ

  have hnorm : ∀ (σ : SL(2, ℤ)), σ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ A ∈ (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)),
        (σ : GL (Fin 2) ℝ) * A * (σ : GL (Fin 2) ℝ)⁻¹ ∈ (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) := by
    intro σ hσ A hA
    obtain ⟨δ, hδ, rfl⟩ := hA
    refine ⟨σ * δ * σ⁻¹, CohCarrier.conj_mem_GammaH N H ⟨σ, hσ⟩ ⟨δ, hδ⟩, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hconj : ConjAct.toConjAct g • (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) =
      (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) := by
    ext A
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv]
    constructor
    · intro h
      have := hnorm γ hγ _ h
      rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one] at this
    · intro h
      have hγ' : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := inv_mem hγ
      have := hnorm γ⁻¹ hγ' _ h
      simpa [hg] using this
  refine ⟨{ toFun := ((⇑f : UpperHalfPlane → ℂ) ∣[k] g)
            slash_action_eq' := ?_
            holo' := f.holo'.slash k g
            bdd_at_cusps' := ?_ }, ?_⟩
  · intro A hA
    have e : g * A = (g * A * g⁻¹) * g := by rw [inv_mul_cancel_right]
    rw [← SlashAction.slash_mul, e, SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f _ (hnorm γ hγ A hA)]
  · intro c hc
    have hgc : IsCusp (g • c) (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) := by
      have := hc.smul g
      rwa [hconj] at this
    exact (OnePoint.IsBoundedAt.smul_iff).mp (ModularFormClass.bdd_at_cusps f hgc)
  · rw [hslash]
    rfl

#print axioms solution
