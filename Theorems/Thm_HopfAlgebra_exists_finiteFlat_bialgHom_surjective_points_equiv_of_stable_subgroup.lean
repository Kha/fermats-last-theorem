import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup

set_option autoImplicit false

theorem HopfAlgebra.exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    {L : Type} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L] [Algebra.IsAlgebraic K L]
    (G : Type) [CommRing G] [HopfAlgebra R G] [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (N : Submonoid (WithConv (G →ₐ[R] L)))
    (hN : ∀ (σ : L ≃ₐ[K] L), ∀ f ∈ N, ∀ f' : WithConv (G →ₐ[R] L), (∀ x : G, f'.ofConv x = σ (f.ofConv x)) → f' ∈ N) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ π : G →ₐc[R] H, Function.Surjective π ∧

        (∀ h h' : H →ₐ[R] L, h.comp (π : G →ₐ[R] H) = h'.comp (π : G →ₐ[R] H) → h = h') ∧
        (∀ h h' : WithConv (H →ₐ[R] L),
          WithConv.toConv ((h * h').ofConv.comp (π : G →ₐ[R] H)) =
            WithConv.toConv (h.ofConv.comp (π : G →ₐ[R] H)) * WithConv.toConv (h'.ofConv.comp (π : G →ₐ[R] H))) ∧
        (∀ f : WithConv (G →ₐ[R] L), f ∈ N ↔ ∃ h : H →ₐ[R] L, h.comp (π : G →ₐ[R] H) = f.ofConv) ∧

        Module.finrank R H = Nat.card ↥N := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup.solution
