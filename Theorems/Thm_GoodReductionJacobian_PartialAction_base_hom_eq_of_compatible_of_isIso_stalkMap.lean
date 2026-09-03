import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.PartialAction.base_hom_eq_of_compatible_of_isIso_stalkMap
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι₀ : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι₀]
    (hι₀ : ι₀ ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι₀ hι₀)
    (w : P) (ζ : ↥(pullback f p)) (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w})
    {P'' : Scheme.{u}} (p'' : P'' ⟶ Spec (CommRingCat.of k)) [IsIntegral P''] [IsSeparated p'']
    [LocallyOfFiniteType p'']
    (β : P'' ⟶ P) (hβ : β ≫ p = p'') (W : P.Opens) [IsIso (β ∣_ W)]
    (U' : (pullback f p).Opens) (hU' : U' ≤ a.dom) (hζU' : ζ ∈ U')
    (α' : (U' : Scheme.{u}) ⟶ P'') (hα' : α' ≫ β = (pullback f p).homOfLE hU' ≫ a.hom)
    {P' : Scheme.{u}} [IsIntegral P'] (ν : P' ⟶ P'') [IsIso ((ν ≫ β) ∣_ W)]
    (V' : G.Opens) [Nonempty (V' : Scheme.{u})] (hV' : V' ≤ V)
    (hV'W : Set.range (G.homOfLE hV' ≫ ι₀).base ⊆ (W : Set P))
    (ι' : (V' : Scheme.{u}) ⟶ P') [IsOpenImmersion ι'] (hι'ι₀ : ι' ≫ ν ≫ β = G.homOfLE hV' ≫ ι₀)
    (hι' : ι' ≫ (ν ≫ β) ≫ p = V'.ι ≫ f)
    (a' : PartialAction k f ((ν ≫ β) ≫ p)) (hc' : a'.Compatible L V' ι' hι')
    (w' : P') (hπw' : (ν ≫ β).base w' = w) (hiso : IsIso ((ν ≫ β).stalkMap w'))
    (ζ' : ↥(pullback f ((ν ≫ β) ≫ p))) (hζ' : ζ' ∈ a'.dom)
    (hζ'cl : closure ({ζ'} : Set ↥(pullback f ((ν ≫ β) ≫ p))) =
      (pullback.snd f ((ν ≫ β) ≫ p)).base ⁻¹' closure {w'}) :
    ν.base (a'.hom.base ⟨ζ', hζ'⟩) = α'.base ⟨ζ, hζU'⟩ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.solution
