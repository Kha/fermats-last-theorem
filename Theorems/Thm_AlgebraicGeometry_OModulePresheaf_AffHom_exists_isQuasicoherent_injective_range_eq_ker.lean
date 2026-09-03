import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker
    {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {G F : OModulePresheaf q} (hGq : G.IsQuasicoherent) (hFq : F.IsQuasicoherent)
    (θ : OModulePresheaf.AffHom G F) :
    ∃ (K : OModulePresheaf q) (ι : OModulePresheaf.AffHom K G),
      (IsLocallyNoetherian P → G.IsCoherent → K.IsCoherent) ∧ K.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Injective (ι.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.range (ι.app U) = LinearMap.ker (θ.app U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.solution
