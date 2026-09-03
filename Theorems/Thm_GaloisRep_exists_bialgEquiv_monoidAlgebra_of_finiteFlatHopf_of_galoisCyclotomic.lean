import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

theorem GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Free (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {M : Type} [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (k : ℕ) (htors : ∀ m : M, q ^ k • m = 0)
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ),
      ζ ^ q ^ k = 1 → σ ζ = ζ ^ n σ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), σ • m = n σ • m)
    (hcard : Nat.card M = Module.finrank (GaloisRep.ratLocalizedAt q) H) :
    ∃ φ : H ≃ₐc[GaloisRep.ratLocalizedAt q]
        MonoidAlgebra (GaloisRep.ratLocalizedAt q)
          (WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      ∀ (ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
        (θ : CartierDual (GaloisRep.ratLocalizedAt q) H),
        algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic.solution
