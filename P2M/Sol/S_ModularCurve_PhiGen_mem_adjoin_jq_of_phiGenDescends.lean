module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
public import Definitions.Def_ModularForm_HeckeOperator
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Sol.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff
import P2M.Sol.S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant
import P2M.Sol.S_ModularCurve_cosetPoly_smul
import P2M.Sol.S_ModularCurve_E4_cube_div_discriminant_smul
import P2M.Util
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "jq PhiGen.PhiGenDescends PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff mem_adjoin_jq_of_hasSum_of_slash_invariant cosetPoly_smul E4_cube_div_discriminant_smul"
p2m_open "ModularCurve"

section JT

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  ModularCurve.E4_cube_div_discriminant_smul γ τ

end JT

end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.ModularCurve ModularCurve.PhiGen in
theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : c k ∈ Algebra.adjoin ℚ {jq} := by
  refine ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant (c k) _
    (ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff ℓ ζ hζ c hc k) fun γ τ => ?_
  exact congrArg (fun p : Polynomial ℂ => p.coeff k)
    (ModularCurve.cosetPoly_smul ℓ hℓ.out ModularCurve.jt ModularCurve.jt_smul γ τ)

end
end S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
end P2MW

public section
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : c k ∈ Algebra.adjoin ℚ {jq} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.solution
end
