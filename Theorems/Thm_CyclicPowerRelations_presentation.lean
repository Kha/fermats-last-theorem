import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Maps
import P2M.Util
import P2M.Sol.S_CyclicPowerRelations_presentation

universe u v

theorem CyclicPowerRelations.presentation
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (p r : ℕ) [NeZero r] (hp : 2 ≤ p)
    (hrank : Module.finrank R A = p ^ r)
    (Xv : Fin r → A) (δ : Fin r → R)
    (hrel : ∀ i, Xv i ^ p = δ i • Xv (i + 1))
    (hgen : Algebra.adjoin R (Set.range Xv) = ⊤) :
    (∃ b : Module.Basis (Fin r → Fin p) R A, ∀ d, b d = ∏ i, Xv i ^ (d i : ℕ)) ∧
    Function.Surjective (MvPolynomial.aeval (R := R) Xv) ∧
    RingHom.ker (MvPolynomial.aeval (R := R) Xv).toRingHom
      = Ideal.span (Set.range fun i : Fin r =>
          (MvPolynomial.X i ^ p - MvPolynomial.C (δ i) * MvPolynomial.X (i + 1) : MvPolynomial (Fin r) R)) := by p2m_exact_reverting @_root_.P2MW.S_CyclicPowerRelations_presentation.solution
