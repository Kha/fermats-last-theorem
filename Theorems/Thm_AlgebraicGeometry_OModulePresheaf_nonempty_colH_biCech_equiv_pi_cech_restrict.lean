import Mathlib
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_colH_biCech_equiv_pi_cech_restrict

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_colH_biCech_equiv_pi_cech_restrict
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) (N : Z.Modules)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (p : ℕ)
    (𝔚 : ∀ s : 𝔄.Idx p, ((𝔄.inter s : Z.Opens) : Scheme.{u}).OrderedAffineCover)
    (e : ∀ s : 𝔄.Idx p, 𝔅.ι ≃o (𝔚 s).ι)
    (h𝔚 : ∀ (s : 𝔄.Idx p) (j : 𝔅.ι), (𝔄.inter s).ι ''ᵁ (𝔚 s).U (e s j) = 𝔄.inter s ⊓ 𝔅.U j) :
    Nonempty (DoubleComplex.colH ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) p 0 ≃ₗ[R]
        (∀ s : 𝔄.Idx p, ↥((OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).H0 (𝔚 s)))) ∧
      ∀ q : ℕ, Nonempty (DoubleComplex.colH ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) p (q + 1) ≃ₗ[R]
        (∀ s : 𝔄.Idx p, (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).HSucc (𝔚 s) q)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_colH_biCech_equiv_pi_cech_restrict.solution
