import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_isPullback_of_isPullback_of_iso
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_isPullback_of_isPullback_of_iso
    {g d n : ℕ} {S' : Type} [CommRing S'] (v w : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.Iso v w) :
    ∃ (m : ℕ) (r : Fin m → S'), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (j : Fin m) (wj : PolarisedAbelianScheme g d n (Localization.Away (r j))),
        PolarisedAbelianScheme.IsPullback (algebraMap S' (Localization.Away (r j))) w wj →
        PolarisedAbelianScheme.IsPullback (algebraMap S' (Localization.Away (r j))) v wj := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_isPullback_of_isPullback_of_iso.solution
