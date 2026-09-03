import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_inertia_equivariant_reduceHom_of_variableChange_eq_map
attribute [-instance] ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular
attribute [-simp] FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u v in

theorem WeierstrassCurve.exists_inertia_equivariant_reduceHom_of_variableChange_eq_map
    {F : Type u} {M : Type v} [Field F] [Field M] [DecidableEq M] [Algebra F M]
    (A : ValuationSubring M) [DecidableEq (ResidueField A)]
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hΔ : IsUnit W.Δ) :
    ∃ (θ : (E.baseChange M).toAffine.Point →+ (W.map (residue A)).toAffine.Point)
      (g : (M ≃ₐ[F] M) → VariableChange A),
      (∀ (hΔ' : (W.map (residue A)).Δ ≠ 0) (P : (E.baseChange M).toAffine.Point),
          ∃ Q : (W.map A.subtype).toAffine.Point,
            HEq (Point.vcInvFun κ (E.baseChange M).toAffine P) Q ∧ θ P = reduceHom hΔ' Q) ∧
      (∀ (n : ℕ) (P : (E.baseChange M).toAffine.Point),
          (n : ResidueField A) ≠ 0 → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g σ).map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
          (g σ).map (residue A) • W.map (residue A) = W.map (residue A) ∧
          ∀ P : (E.baseChange M).toAffine.Point,
            HEq (Point.vcInvFun ((g σ).map (residue A)) (W.map (residue A)).toAffine (θ P))
              (θ (Point.map (σ : M →ₐ[F] M) P))) ∧
      (∀ (σ τ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
          (hτ : τ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (⟨τ, hτ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g (σ * τ)).map (residue A) = (g σ).map (residue A) * (g τ).map (residue A)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_inertia_equivariant_reduceHom_of_variableChange_eq_map.solution
