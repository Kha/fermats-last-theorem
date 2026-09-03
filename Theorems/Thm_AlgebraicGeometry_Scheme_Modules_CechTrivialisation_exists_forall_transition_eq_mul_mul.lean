import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_forall_transition_eq_mul_mul
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (c c' : ∀ a : 𝒱.ι, Γ(Y, 𝒱.U a)) (hc : ∀ a : 𝒱.ι, c a * c' a = 1) :
    ∃ τ' : Scheme.Modules.CechTrivialisation 𝒱 𝓜,
      (∀ a : 𝒱.ι, Scheme.Modules.unitAutSection (𝒱.U a) ((τ a).symm ≪≫ τ' a) = c a) ∧
      ∀ s : 𝒱.Idx 1,
        τ'.transition s = τ.transition s *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 0)).op).hom (c' (s.1 0)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 1)).op).hom (c (s.1 1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul.solution
