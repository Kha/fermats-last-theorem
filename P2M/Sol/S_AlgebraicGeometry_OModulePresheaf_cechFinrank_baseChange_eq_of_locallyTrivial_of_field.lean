import Mathlib
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_baseChange_eq_of_locallyTrivial_of_field
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    {k₀ : Type u} [Field k₀] {X : Scheme.{u}} (π : X ⟶ Spec (.of k₀)) [IsSeparated π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (k : Type u) [Field k] [Algebra k₀ k] (n : ℕ) :
    (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k₀ k))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap k₀ k))).obj M)).cechFinrank (𝒰.baseChange π k) n =
      (OModulePresheaf.ofModules π M).cechFinrank 𝒰 n := by
  obtain ⟨-, hflat⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial π 𝒰 M htriv k
  obtain ⟨⟨e0⟩, eS⟩ := hflat inferInstance
  cases n with
  | zero =>
    rw [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero, e0.finrank_eq, Module.finrank_baseChange]
  | succ i =>
    obtain ⟨e⟩ := eS i
    rw [OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ, e.finrank_eq, Module.finrank_baseChange]
