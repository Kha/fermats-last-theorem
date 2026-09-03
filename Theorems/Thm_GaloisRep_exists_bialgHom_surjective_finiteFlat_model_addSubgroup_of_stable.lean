import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable

set_option autoImplicit false

theorem GaloisRep.exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = σ • e f)
    {T : Type} (act : T → (N →+ N)) (φ : T → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : ∀ (t : T) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (φ t h)) → e g = act t (e f))
    (N' : AddSubgroup N)
    (hN'gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ N', σ • x ∈ N')
    (hN'act : ∀ t : T, ∀ x ∈ N', act t x ∈ N') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H')
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) H') (_ : Module.Free (GaloisRep.ratLocalizedAt p) H')
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H')
      (π : H →ₐc[GaloisRep.ratLocalizedAt p] H')
      (e' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥N')
      (φ' : T → (H' →ₐ[GaloisRep.ratLocalizedAt p] H')),
      Function.Surjective π ∧
      (∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        ((e' f : ↥N') : N) =
          e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H')))) ∧
      (∀ t : T, (φ' t).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H') =
        (π : H →ₐ[GaloisRep.ratLocalizedAt p] H').comp (φ t)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable.solution
