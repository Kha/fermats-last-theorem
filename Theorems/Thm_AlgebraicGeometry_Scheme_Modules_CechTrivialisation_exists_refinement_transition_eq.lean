import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_refinement_transition_eq
    {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒱 : Y.OrderedAffineCover) (𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝒱.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒱.U (lam w))
    (𝓜 : Y.Modules) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    ∃ τ' : Scheme.Modules.CechTrivialisation 𝒲 ((Scheme.Modules.pullback h).obj 𝓜),

      (∀ w : 𝒲.ι, τ' w =
        ((Scheme.Modules.pullbackComp (𝒲.U w).ι h).app 𝓜) ≪≫
          ((Scheme.Modules.pullbackCongr
              (show (𝒲.U w).ι ≫ h = (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w))) ≫ (𝒱.U (lam w)).ι by
                rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι])).app 𝓜) ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w))) (𝒱.U (lam w)).ι).app 𝓜).symm ≪≫
          (Scheme.Modules.pullback (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w)))).mapIso (τ (lam w)) ≪≫
          Scheme.Modules.pullbackUnitIso (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w)))) ∧

      (∀ s : 𝒲.Idx 1, lam (s.1 0) = lam (s.1 1) → τ'.transition s = 1) ∧

      (∀ (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)), lam (s.1 0) < lam (s.1 1) →
        τ'.transition s =
          (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
            ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj)))) ∧

      (∀ (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)), lam (s.1 1) < lam (s.1 0) →
        τ'.transition s *
          (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
            ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj))) = 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.solution
