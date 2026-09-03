import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map
    {X X' : Scheme.{u}} (g : X' ⟶ X) {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    (hg : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {M : X.Modules} {σ : M ⟶ M} {c : R} (hσ : IsBaseScalar f σ c) :
    IsBaseScalar f' ((Scheme.Modules.pullback g).map σ) (φ c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map.solution
