import Mathlib
import Definitions.Def_HeckeGalois_MazurCase1BundleNoBT1
import P2M.Util
import P2M.Sol.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq

universe u v w
set_option autoImplicit false
attribute [local instance] Ideal.Quotient.field in
open ModularCurve in

theorem ModularCurve.MazurII142.OdaDictionaryNoBT1.finrank_eq_two_of_finrank_ker_frob_eq
    {𝕋 : Type u} [CommRing 𝕋] {J : Type v} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋} [𝔪.IsMaximal]
    {Vrep : Type w} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
    {HDR : Type w} [AddCommGroup HDR] [Module (𝕋 ⧸ 𝔪) HDR]
    {MV : Type w} [AddCommGroup MV] [Module (𝕋 ⧸ 𝔪) MV]
    {H0Ω : Type w} [AddCommGroup H0Ω] [Module (𝕋 ⧸ 𝔪) H0Ω]
    {H1O : Type w} [AddCommGroup H1O] [Module (𝕋 ⧸ 𝔪) H1O]
    (P : MazurII142.OdaDictionaryNoBT1 𝕋 J 𝔪 (𝕋 ⧸ 𝔪) Vrep HDR MV H0Ω H1O)
    [FiniteDimensional (𝕋 ⧸ 𝔪) HDR]
    (hrank : Module.finrank (𝕋 ⧸ 𝔪) ↥(LinearMap.ker P.DMV.frob) =
      Module.finrank (𝕋 ⧸ 𝔪) (MV ⧸ LinearMap.range P.DMV.ver))
    (hlayer : P.FontaineLayer)
    (h94 : Module.finrank (𝕋 ⧸ 𝔪) H1O ≤ 1)
    (hdimV : Module.finrank (𝕋 ⧸ 𝔪) Vrep = 2) :
    Module.finrank (𝕋 ⧸ 𝔪) ↥(Submodule.torsionBySet 𝕋 J 𝔪) = 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.solution
