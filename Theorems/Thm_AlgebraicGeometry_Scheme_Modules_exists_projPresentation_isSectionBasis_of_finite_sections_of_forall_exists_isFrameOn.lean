import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (hX : Nonempty X)
    (𝓝 : X.Modules) (h𝓝 : Scheme.Modules.IsInvertible 𝓝)
    (hfin : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
      Module.Finite k Γ(𝓝, ⊤))
    (hgen : ∀ x : X, ∃ (s : Γ(𝓝, ⊤)) (U : X.Opens), x ∈ U ∧ Scheme.Modules.IsFrameOn s U) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N), Scheme.Modules.IsSectionBasis f 𝓝 𝔓.σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn.solution
