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
import P2M.Sol.S_Deformation_HondaSystem_SplitCoordinates_map_mem_fontaineFunctor_and_described

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem Deformation.HondaSystem.SplitCoordinates.map_mem_fontaineFunctor_and_described
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful)
    (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    [CommRing g'] [Algebra 𝓞 g'] [IsAdicComplete (Ideal.span {(p : g')}) g']
    (hpg' : (p : g') ∈ nonZeroDivisors g') (φ : g →ₐ[𝓞] g')
    (z : (H₁.L →ₗ[𝓞] Localization.Away (p : g)) ×
      ((Fin r → 𝓞) →+ Deformation.UnipotentWittCovector p (TensorProduct 𝓞 (ZMod p) g)))
    (hz : z ∈ Deformation.HondaSystem.fontaineFunctor p H₁ (ZMod p)
      (Algebra.TensorProduct.includeRight : g →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g).toRingHom)
    (v : ℕ) (f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
    (y : 𝒮.Et v →ₐ[𝓞] g) (x : Fin 𝒮.d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)
    (hη : z.2 = (Deformation.DieudonneModule.eval (ZMod p) p
        ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp
          (𝒮.Θ v : G v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v))).comp (π v))
    (he : e.comp (𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐ[ZMod p] 𝒮.Ge v) =
        Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y)
    (hf : ∀ i, f (𝒮.κ v (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i)
    (hξ : ∀ i, z.1 (𝒮.α i) =
        Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
        Deformation.PLoc.wSeries p (fun k => y (𝒮.ĉ i k v))) :

    ((Deformation.PLoc.mapLinear p φ).comp z.1,
      (Deformation.UnipotentWittCovector.map p
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ).toRingHom).comp z.2) ∈
      Deformation.HondaSystem.fontaineFunctor p H₁ (ZMod p)
        (Algebra.TensorProduct.includeRight : g' →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g').toRingHom ∧

    ((∃ v₀ : ℕ, ∀ m : Fin r → 𝓞, z.2 ((p : 𝓞) ^ v₀ • m) = 0) →
      ∃ v₀ : ℕ, ∀ m : Fin r → 𝓞, ((Deformation.UnipotentWittCovector.map p
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ).toRingHom).comp z.2) ((p : 𝓞) ^ v₀ • m) = 0) ∧

    (Deformation.UnipotentWittCovector.map p
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ).toRingHom).comp z.2 =
      (Deformation.DieudonneModule.eval (ZMod p) p
        ((Algebra.TensorProduct.lift
            ((Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ).comp f)
            ((Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ).comp e)
            (fun _ _ => Commute.all _ _)).comp
          (𝒮.Θ v : G v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v))).comp (π v) ∧

    ((Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ).comp e).comp
        (𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐ[ZMod p] 𝒮.Ge v) =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ.comp y) ∧

    (∀ i, ((Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ).comp f) (𝒮.κ v (X i)) =
      (1 : ZMod p) ⊗ₜ[𝓞] φ (x i)) ∧

    (∀ i, ((Deformation.PLoc.mapLinear p φ).comp z.1) (𝒮.α i) =
      Deformation.PLoc.wSeries p
          (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g')}) (φ ∘ x) (𝒮.a i n)) +
        Deformation.PLoc.wSeries p (fun k => (φ.comp y) (𝒮.ĉ i k v))) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_mem_fontaineFunctor_and_described.solution
