import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection_of_operators

theorem GaloisRep.exists_finiteFlat_sub_of_equivariant_injection_of_operators (p : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra (GaloisRep.ratLocalizedAt p) G]
    [Module.Finite (GaloisRep.ratLocalizedAt p) G] [Module.Flat (GaloisRep.ratLocalizedAt p) G]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    {T : Type} (act : T → M →+ M)
    (φ : T → (G →ₐ[GaloisRep.ratLocalizedAt p] G))
    (hφ_aug : ∀ t : T,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) G) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) G)).comap (φ t))
    (hφ : ∀ (t : T) (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = f (φ t x)) → e g = act t (e f))
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (ι : N →+ M) (hι : Function.Injective ι)
    (hι_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : N), ι (σ • n) = σ • (ι n))
    (actN : T → N →+ N) (hι_act : ∀ (t : T) (n : N), ι (actN t n) = act t (ι n)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f)) ∧
        ∃ φ' : T → (H →ₐ[GaloisRep.ratLocalizedAt p] H),
          (∀ t : T,
            RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
              (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ' t)) ∧
          ∀ (t : T) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : H, g x = f (φ' t x)) → e' g = actN t (e' f) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection_of_operators.solution
