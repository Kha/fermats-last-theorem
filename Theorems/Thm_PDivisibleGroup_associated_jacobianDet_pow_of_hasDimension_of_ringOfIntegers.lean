import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ} (hn : G.HasDimension n) (v : ℕ)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K))
    (e : (MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K) ⧸ Ideal.span (Set.range f)) ≃ₐ[PadicAlgCl.ringOfIntegers p K]
      G.level v) :
    Associated (e (Ideal.Quotient.mk _ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))
      (((p : ℕ) : G.level v) ^ (n * v)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers.solution
