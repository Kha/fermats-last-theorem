import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
    (p : ℕ) [Fact p.Prime]
    (G : Type) [CommRing G] [HopfAlgebra ℤ_[p] G] [Module.Finite ℤ_[p] G] [Module.Flat ℤ_[p] G]
    [Coalgebra.IsCocomm ℤ_[p] G]
    {M : Type} [AddCommGroup M] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    (N : AddSubgroup M) (hN : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M), m ∈ N → σ • m ∈ N) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ (ϖ : G →ₐc[ℤ_[p]] H), Function.Surjective ϖ ∧
        (∀ h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) ∈ N) ∧
        (∀ m ∈ N, ∃! h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) = m) ∧
        (∀ h h' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv (h * h')).comp (ϖ : G →ₐ[ℤ_[p]] H))) =
            e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) +
              e (WithConv.toConv ((WithConv.ofConv h').comp (ϖ : G →ₐ[ℤ_[p]] H)))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup.solution
