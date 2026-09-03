import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (N : A ⟶ A) (hN : N ≫ f = f) [IsIso N]
    (𝓛 𝓜 : A.Modules) (k' : Type u) [Field k'] (sk : k →+* k') :
    ((∃ s : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓜, s ≠ 0) →
      ∃ t : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj
            ((Scheme.Modules.pullback N).obj 𝓜), t ≠ 0) ∧
    ((∃ u : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛 ⊗
            (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj
              ((Scheme.Modules.pullback N).obj 𝓜), u ≠ 0) →
      ∃ v : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj
            (𝓛 ⊗ (Scheme.Modules.pullback N).obj 𝓜), v ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor.solution
