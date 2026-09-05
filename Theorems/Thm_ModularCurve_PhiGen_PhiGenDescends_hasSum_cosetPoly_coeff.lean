module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
public import Definitions.Def_ModularForm_HeckeOperator
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import P2M.Util
public import P2M.Sol.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff

@[expose] public section

theorem ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c) (k : ℕ) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (((Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeDiagMatrix ℓ • τ) ^ 3 / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeMatrix ℓ (b : ℕ) • τ) ^ 3 / ModularForm.discriminant (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)))).coeff k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.solution
