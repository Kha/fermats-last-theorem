import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (M : FullLattice 𝒪 K₀)
    (N₁ N₂ : Submodule B (latticeBaseChange 𝒪 K₀ B M))
    (h₁ : Module.Invertible B (latticeBaseChange 𝒪 K₀ B M ⧸ N₁))
    (h₂ : Module.Invertible B (latticeBaseChange 𝒪 K₀ B M ⧸ N₂))
    (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (Localization.AtPrime 𝔭)) M N₁ =
      lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (Localization.AtPrime 𝔭)) M N₂) :
    ∃ f : B, f ∉ 𝔭 ∧
      ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away f C],
        lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₁ = lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq.solution
