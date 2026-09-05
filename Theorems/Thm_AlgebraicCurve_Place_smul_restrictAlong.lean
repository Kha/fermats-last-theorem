module

public import Definitions.Def_AlgebraicCurve_Correspondence
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_Place_smul_restrictAlong

@[expose] public section

open AlgebraicCurve

theorem AlgebraicCurve.Place.smul_restrictAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral) (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).restrictAlong α hα = τ • W.restrictAlong β hβ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_smul_restrictAlong.solution
