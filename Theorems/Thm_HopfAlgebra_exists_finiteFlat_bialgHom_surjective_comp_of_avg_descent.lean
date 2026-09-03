import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent

theorem HopfAlgebra.exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {L : Type} [Field L] [Algebra R L] [IsAlgClosed L]
    (hRL : Function.Injective (algebraMap R L))
    (G : Type) [CommRing G] [HopfAlgebra R G]
    [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (K : Finset (G →ₐ[R] L))
    (hKone : (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R G) ∈ K)
    (hKmul : ∀ k ∈ K, ∀ k' ∈ K,
      WithConv.ofConv (WithConv.toConv k * WithConv.toConv k') ∈ K)
    (hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode R)
    (hdesc : ∀ g : G, ∃ (r : R) (g' : G), r ≠ 0 ∧
      r • (∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id R G)).comp
        (Bialgebra.comulAlgHom R G) g) = (1 : L) ⊗ₜ[R] g') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ ι : H' →ₐc[R] G,
        Function.Surjective (fun φ : G →ₐ[R] L => φ.comp (ι : H' →ₐ[R] G)) ∧
        ∀ φ ψ : G →ₐ[R] L, φ.comp (ι : H' →ₐ[R] G) = ψ.comp (ι : H' →ₐ[R] G) ↔
          ∃ k ∈ K, ψ = WithConv.ofConv (WithConv.toConv k * WithConv.toConv φ) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.solution
