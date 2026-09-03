import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Deformation_SplitCoordinates
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem Deformation.HondaSystem.SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful)
    (Φ : MvFormalGroup 𝒮.d 𝓞)
    (hΦ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin 𝒮.d → g), (∀ j, IsNilpotent (x j)) → (∀ j, IsNilpotent (y j)) →
      ∃ (v : ℕ) (fx fy : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
        (∀ j, fx (𝒮.κ v (X j)) = (1 : ZMod p) ⊗ₜ[𝓞] x j) ∧
        (∀ j, fy (𝒮.κ v (X j)) = (1 : ZMod p) ⊗ₜ[𝓞] y j) ∧
        ∀ i, (WithConv.toConv fx * WithConv.toConv fy).ofConv (𝒮.κ v (X i)) =
          (1 : ZMod p) ⊗ₜ[𝓞] MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i)) :
    Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀ := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.solution
