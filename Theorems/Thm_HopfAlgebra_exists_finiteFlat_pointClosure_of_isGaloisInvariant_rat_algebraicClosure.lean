import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure

set_option autoImplicit false

theorem HopfAlgebra.exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (Γ : Submonoid (WithConv (H →ₐ[R] AlgebraicClosure ℚ)))
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ν : WithConv (H →ₐ[R] AlgebraicClosure ℚ)), ν ∈ Γ →
      WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars R).comp
        (WithConv.ofConv ν)) ∈ Γ) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H') (π : H →ₐc[R] H'),
      Function.Surjective π ∧ Module.Finite R H' ∧ Module.Flat R H' ∧
      Coalgebra.IsCocomm R H' ∧
      (RingHom.ker π = ⨅ ν ∈ Γ, RingHom.ker (WithConv.ofConv ν)) ∧
      ∀ (T : Type) [CommRing T] [Algebra R T] (ι : T →ₐ[R] AlgebraicClosure ℚ),
        Function.Injective ι →
        ∀ φ : H →ₐ[R] T,
          (∃ φ' : H' →ₐ[R] T, φ'.comp (π : H →ₐ[R] H') = φ) ↔
            WithConv.toConv (ι.comp φ) ∈ Γ := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure.solution
