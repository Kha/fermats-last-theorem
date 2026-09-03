import Mathlib
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
import P2M.Sol.S_Rep_coind_pairing_adjoint

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.coind_pairing_adjoint {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.FiniteIndex] {M D N : Rep.{u} k G}
    (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (ιM : M ⟶ Rep.coind S.subtype (Rep.res S.subtype M))
    (hιM : ∀ (m : M) (g : G), ((ιM.hom m : Rep.coind S.subtype (Rep.res S.subtype M)) : G → M) g = M.ρ g m)
    (τM : Rep.coind S.subtype (Rep.res S.subtype M) ⟶ M)
    (hτM : ∀ f : Rep.coind S.subtype (Rep.res S.subtype M),
      τM.hom f = ∑ᶠ q : G ⧸ S, M.ρ q.out ((f : G → M) (q.out)⁻¹))
    (ιD : D ⟶ Rep.coind S.subtype (Rep.res S.subtype D))
    (hιD : ∀ (d : D) (g : G), ((ιD.hom d : Rep.coind S.subtype (Rep.res S.subtype D)) : G → D) g = D.ρ g d)
    (τD : Rep.coind S.subtype (Rep.res S.subtype D) ⟶ D)
    (hτD : ∀ f : Rep.coind S.subtype (Rep.res S.subtype D),
      τD.hom f = ∑ᶠ q : G ⧸ S, D.ρ q.out ((f : G → D) (q.out)⁻¹))
    (τN : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ N)
    (hτN : ∀ f : Rep.coind S.subtype (Rep.res S.subtype N),
      τN.hom f = ∑ᶠ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹))
    (Ψ : Rep.coind S.subtype (Rep.res S.subtype M) →ₗ[k] Rep.coind S.subtype (Rep.res S.subtype D) →ₗ[k] N)
    (hΨ : ∀ (f : Rep.coind S.subtype (Rep.res S.subtype M)) (g : Rep.coind S.subtype (Rep.res S.subtype D))
      (w : Rep.coind S.subtype (Rep.res S.subtype N)),
      (∀ h : G, (w : G → N) h = φ ((f : G → M) h) ((g : G → D) h)) → Ψ f g = τN.hom w) :
    (∀ (m : M) (y : Rep.coind S.subtype (Rep.res S.subtype D)), Ψ (ιM.hom m) y = φ m (τD.hom y)) ∧
    (∀ (x : Rep.coind S.subtype (Rep.res S.subtype M)) (d : D), Ψ x (ιD.hom d) = φ (τM.hom x) d) := by p2m_exact_reverting @_root_.P2MW.S_Rep_coind_pairing_adjoint.solution
