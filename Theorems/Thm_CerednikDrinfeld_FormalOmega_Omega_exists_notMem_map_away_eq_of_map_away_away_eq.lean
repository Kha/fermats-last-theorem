import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_Omega_exists_notMem_map_away_eq_of_map_away_away_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.exists_notMem_map_away_eq_of_map_away_away_eq
    {𝒪 : Type} [CommRing 𝒪] (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime)
    (e : B) (he : e ∉ 𝔭) (f : Localization.Away e) (hf : f ∉ Ideal.map (algebraMap B (Localization.Away e)) 𝔭)
    (P P' : (Omega K₀ π).obj B)
    (h : (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 (Localization.Away e) (Localization.Away f))
            ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away e)) P)
       = (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 (Localization.Away e) (Localization.Away f))
            ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away e)) P')) :
    ∃ c : B, c ∉ 𝔭 ∧ (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) P
      = (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) P' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_notMem_map_away_eq_of_map_away_away_eq.solution
