module

public import Definitions.Def_ModularCurve_AtkinLehnerPartial
public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_GeometricBaseChange
public import P2M.Util
public import P2M.Sol.S_ModularCurve_geomAut_atkinLehner_comp_legs

@[expose] public section

open ModularCurve
theorem ModularCurve.geomAut_atkinLehner_comp_legs (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ)) (hσ : IsAtkinLehnerAutFull N ℓ σ) : (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeAlphaBar L N ℓ) = heckeBetaBar L N ℓ ∧ (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeBetaBar L N ℓ) = heckeAlphaBar L N ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_geomAut_atkinLehner_comp_legs.solution
