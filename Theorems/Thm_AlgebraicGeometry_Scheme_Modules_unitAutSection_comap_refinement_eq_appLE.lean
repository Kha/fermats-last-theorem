import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.unitAutSection_comap_refinement_eq_appLE
    {X X' X₀ X₀' : Scheme.{u}}
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (h : X' ⟶ X) (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (M : X.Modules) (τ : Scheme.Modules.CechTrivialisation 𝒰 M)
    (τ' : Scheme.Modules.CechTrivialisation 𝒲 ((Scheme.Modules.pullback h).obj M))
    (w : 𝒲.ι) (hτ' : τ' w = (((Scheme.Modules.pullbackComp (𝒲.U w).ι h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr
              (show (𝒲.U w).ι ≫ h = (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) ≫ (𝒰.U (lam w)).ι by
                rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι])).app M) ≪≫
          ((Scheme.Modules.pullbackComp (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) (𝒰.U (lam w)).ι).app M).symm ≪≫
          (Scheme.Modules.pullback (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w)))).mapIso (τ (lam w)) ≪≫
          Scheme.Modules.pullbackUnitIso (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w)))))
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf) :
    Scheme.Modules.unitAutSection ((𝒲.comap g').U w)
        ((τ'.comap g' w).symm ≪≫
          ((Scheme.Modules.pullback ((𝒲.comap g').U w).ι).mapIso (((Scheme.Modules.pullbackComp g' h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr hh₀.symm).app M) ≪≫
          ((Scheme.Modules.pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso h₀) ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒲.comap g').U w).ι)) =
      (h₀.appLE ((𝒰.comap g).U (lam w)) ((𝒲.comap g').U w)
          (show g' ⁻¹ᵁ 𝒲.U w ≤ h₀ ⁻¹ᵁ (g ⁻¹ᵁ 𝒰.U (lam w)) by
            rw [← Scheme.Hom.comp_preimage, hh₀, Scheme.Hom.comp_preimage]
            exact fun p hp => hlam w hp)).hom
        (Scheme.Modules.unitAutSection ((𝒰.comap g).U (lam w))
          ((τ.comap g (lam w)).symm ≪≫
            ((Scheme.Modules.pullback ((𝒰.comap g).U (lam w)).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U (lam w)).ι))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.solution
