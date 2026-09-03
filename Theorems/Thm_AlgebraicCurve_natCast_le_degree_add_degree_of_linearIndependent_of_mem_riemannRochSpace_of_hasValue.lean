import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (hdeg : ∀ v : Place k F, v.deg = 1)
    (hfin : ∀ D : Divisor k F, FiniteDimensional k ↥(LSpace D))
    (hRR : ∀ D : Divisor k F, 2 * (genusFF k F : ℤ) - 1 ≤ D.degree → (ell D : ℤ) = D.degree + 1 - genusFF k F)
    (W : Finset (Place k F)) (NP : Set (Place k F × Place k F))
    (hNP : ∀ w ∈ W, ∃ v' : Place k F, (w, v') ∈ NP)
    (D₁ D₂ : Divisor k F) (hD₁ : ∀ w ∈ W, D₁ w = 0)
    (hdeg₁ : 2 * (genusFF k F : ℤ) - 1 + W.card ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF k F : ℤ) - 1 ≤ D₂.degree)
    {m : ℕ} (x : Fin m → F × F)
    (hx₁ : ∀ a, ∀ v : Place k F, (x a).1 = 0 ∨ -D₁ v ≤ v.ord (x a).1)
    (hx₂ : ∀ a, ∀ v : Place k F, (x a).2 = 0 ∨ -D₂ v ≤ v.ord (x a).2)
    (hxNP : ∀ a, ∀ nd ∈ NP, ∃ c : k, nd.1.HasValue (x a).1 c ∧ nd.2.HasValue (x a).2 c)
    (hli : LinearIndependent k x) :
    (m : ℤ) ≤ D₁.degree + D₂.degree + 2 - 2 * (genusFF k F : ℤ) - W.card := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue.solution
