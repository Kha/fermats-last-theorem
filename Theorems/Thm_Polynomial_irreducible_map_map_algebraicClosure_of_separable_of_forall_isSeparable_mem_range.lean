import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range

set_option autoImplicit false

universe u v

theorem Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (hsc : ∀ θ : L, IsSeparable K θ → θ ∈ (algebraMap K L).range)
    {d : ℕ} (x : Fin d → L) (hx : AlgebraicIndependent K x) (y : L)
    (F : Polynomial (MvPolynomial (Fin d) K)) (hFm : F.Monic)
    (hFirr : Irreducible (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))))
    (hFsep : (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))).Separable)
    (hroot : F.eval₂ (MvPolynomial.aeval x : MvPolynomial (Fin d) K →ₐ[K] L).toRingHom y = 0) :
    Irreducible (F.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.solution
