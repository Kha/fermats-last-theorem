module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul

@[expose] public section

theorem ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) : ModularForm.discriminant (γ • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ) = ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul.solution
