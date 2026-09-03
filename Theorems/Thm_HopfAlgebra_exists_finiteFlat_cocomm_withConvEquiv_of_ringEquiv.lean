import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv

theorem HopfAlgebra.exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv
    (R : Type) [CommRing R] (S : Type) [CommRing S] (φ : R ≃+* S)
    [Algebra R (AlgebraicClosure ℚ)] [Algebra S (AlgebraicClosure ℚ)]
    (hφ : ∀ r, algebraMap R (AlgebraicClosure ℚ) r = algebraMap S (AlgebraicClosure ℚ) (φ r))
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (H : Type) [CommRing H] [HopfAlgebra S H]
    (hHfin : Module.Finite S H) (hHflat : Module.Flat S H)
    (hHcocomm : Coalgebra.IsCocomm S H)
    (eH : WithConv (H →ₐ[S] AlgebraicClosure ℚ) ≃ N)
    (heH_add : ∀ f g, eH (f * g) = eH f + eH g)
    (heH_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[S] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → eH g = σ • (eH f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ e' : WithConv (H' →ₐ[R] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H' →ₐ[R] AlgebraicClosure ℚ)),
          (∀ h : H', g h = σ (f h)) → e' g = σ • (e' f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv.solution
