module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeLocalized
public import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral

@[expose] public section

set_option autoImplicit false

open ModularCurve
open ModularCurve.NodeLocalized
theorem ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ)}) g)
    (x₀ : A) (hb : red x₀ ^ (q ^ 2) ≠ red x₀) :
    g ∈ modularLocalizedAtPoint (1 * q) A.toSubring red (red x₀) (red x₀ ^ q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral.solution
