import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} {Y : ι → Scheme.{u}} (b : ∀ j, Y j ⟶ X)
    [∀ j, IsOpenImmersion (b j)]
    (hcov : ⨆ j, Scheme.Hom.opensRange (b j) = ⊤)
    (hdisj : ∀ j l, j ≠ l → Scheme.Hom.opensRange (b j) ⊓ Scheme.Hom.opensRange (b l) = ⊥)
    (e : ∀ j, (Scheme.Modules.pullback (b j)).obj M ≅ (Scheme.Modules.pullback (b j)).obj N) :
    ∃! φ : M ≅ N, ∀ j, (Scheme.Modules.pullback (b j)).mapIso φ = e j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot.solution
