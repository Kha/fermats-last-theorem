import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq
import P2M.Util
namespace P2MW.S_HopfAlgebra_exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible

set_option maxHeartbeats 3200000

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra R (AlgebraicClosure ℚ)] [IsScalarTower R ℚ (AlgebraicClosure ℚ)]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R))
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    (hHfin : Module.Finite (GaloisRep.ratLocalizedAt p) H)
    (hHflat : Module.Flat (GaloisRep.ratLocalizedAt p) H)
    (hHcocomm : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H)
    (eH : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (heH_add : ∀ f g, eH (f * g) = eH f + eH g)
    (heH_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → eH g = σ • (eH f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ e' : WithConv (H' →ₐ[R] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H' →ₐ[R] AlgebraicClosure ℚ)),
          (∀ h : H', g h = σ (f h)) → e' g = σ • (e' f) := by
  have hrange :=
    IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible R p hp
  exact HopfAlgebra.exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq
    R p hrange H hHfin hHflat hHcocomm eH heH_add heH_act
