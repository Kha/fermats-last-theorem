import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isSectionBasis_of_isSectionBasisOn_pullback_id

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isSectionBasis_of_isSectionBasisOn_pullback_id
    {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules) {m : ℕ}
    (σ : Fin m → Γ(M, ⊤))
    (h : Scheme.Modules.IsSectionBasisOn f ((Scheme.Modules.pullback (𝟙 X)).obj M) ((𝟙 X) ⁻¹ᵁ ⊤)
      (fun i => Scheme.Modules.pullbackLocalSection (𝟙 X) (σ i))) :
    Scheme.Modules.IsSectionBasis f M σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isSectionBasis_of_isSectionBasisOn_pullback_id.solution
