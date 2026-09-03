import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial

theorem GaloisRep.exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {M : Type} [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (htriv : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), σ • m = m)
    (htors : ∃ k : ℕ, ∀ m : M, q ^ k • m = 0)
    (hcard : Nat.card M = Module.finrank (GaloisRep.ratLocalizedAt q) H) :
    (∀ (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) (x : H),
        (f x) ∈ (algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ)).range) ∧
    ∃ φ : H ≃ₐ[GaloisRep.ratLocalizedAt q]
        (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → GaloisRep.ratLocalizedAt q),
      ∀ (x : H) (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
        algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (φ x f) = f x := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial.solution
