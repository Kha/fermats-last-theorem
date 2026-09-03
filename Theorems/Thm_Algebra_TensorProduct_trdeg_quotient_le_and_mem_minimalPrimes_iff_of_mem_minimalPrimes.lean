import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.TensorProduct.trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
    {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    [Algebra.FiniteType R A']
    (𝔓 : Ideal (A ⊗[R] A')) [𝔓.IsPrime]
    (h : 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom ∈
      ((𝔓.under R).map (algebraMap R A')).minimalPrimes) :
    Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) ≤
        Algebra.trdeg
          (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom).under R)
          (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom) ∧
      (𝔓 ∈ ((𝔓.under A).map (algebraMap A (A ⊗[R] A'))).minimalPrimes ↔
        Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) =
          Algebra.trdeg
            (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom).under R)
            (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes.solution
