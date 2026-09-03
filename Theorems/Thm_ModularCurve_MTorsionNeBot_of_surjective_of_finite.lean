import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
import P2M.Sol.S_ModularCurve_MTorsionNeBot_of_surjective_of_finite

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.MTorsionNeBot.of_surjective_of_finite {𝕋 : Type*} [CommRing 𝕋]
    {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] (𝔪 : Ideal 𝕋)
    [Finite N] (f : N →ₗ[𝕋] N'') (hf : Function.Surjective f) :
    MTorsionNeBot 𝕋 N'' 𝔪 → MTorsionNeBot 𝕋 N 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MTorsionNeBot_of_surjective_of_finite.solution
