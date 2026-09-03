import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero

set_option autoImplicit false

theorem AlgebraicCurve.Place.existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x y : F) (f : MvPolynomial (Fin 2) K)
    (hf : MvPolynomial.aeval ![x, y] f = 0)
    (hker : ∀ g : MvPolynomial (Fin 2) K, MvPolynomial.aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
    (hF : Subfield.closure (Set.range (algebraMap K F) ∪ {x, y}) = ⊤)
    (a b : K) (hab : MvPolynomial.eval ![a, b] f = 0)
    (hsmooth : MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 1 f) ≠ 0) :
    ∃! v : AlgebraicCurve.Place K F,
      x - algebraMap K F a ∈ v.toValuationSubring.nonunits ∧
        y - algebraMap K F b ∈ v.toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero.solution
