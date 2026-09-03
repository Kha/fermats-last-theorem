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
import P2M.Sol.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem Deformation.HondaSystem.exists_bijective_tensorProduct_specialFibre_of_cocycle
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (h𝒮 : 𝒮.Lawful)
    (Φ : MvFormalGroup 𝒮.d 𝓞) [Φ.IsComm] (hΦ : Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀)
    (c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
    (hc₂p : ∀ v i, c₂ v i ∈ Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)})

    (L : ℕ → Type u) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ι : ∀ v, 𝒮.Et v →ₐc[𝓞] L v)
    (Ψ : ∀ v, MvPowerSeries (Fin 𝒮.d) 𝓞 →ₐ[𝓞] L v)
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * (𝒮.hc + 𝒮.he)))
    (hιt : ∀ v, (t v).comp (ι (v + 1)) = (ι v).comp (𝒮.st v))
    (hΨt : ∀ v, ((t v : L (v + 1) →ₐc[𝓞] L v) : L (v + 1) →ₐ[𝓞] L v).comp (Ψ (v + 1)) = Ψ v)
    (hΨε : ∀ v i, Coalgebra.counit (R := 𝓞) (Ψ v (X i)) = 0)
    (hΨtors : ∀ v i, Ψ v (Φ.nthSeries (p ^ v) i) ∈ Ideal.span {(p : L v)})
    (hgen : ∀ v, Function.Surjective
        (Algebra.TensorProduct.lift (ι v : 𝒮.Et v →ₐ[𝓞] L v) (Ψ v) (fun _ _ => Commute.all _ _)))
    (hcomul : ∀ v i, Coalgebra.comul (R := 𝓞) (Ψ v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
          (Sum.elim (fun j => Ψ v (X j) ⊗ₜ[𝓞] (1 : L v))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
              (Sum.elim (fun j => (1 : L v) ⊗ₜ[𝓞] Ψ v (X j))
                (fun j => Algebra.TensorProduct.map (ι v : 𝒮.Et v →ₐ[𝓞] L v) (ι v : 𝒮.Et v →ₐ[𝓞] L v)
                  (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i)) :
    ∃ ee : ∀ v, 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐc[ZMod p] ZMod p ⊗[𝓞] L v,
      (∀ v, Function.Bijective (ee v)) ∧
      (∀ v (F : MvPowerSeries (Fin 𝒮.d) 𝓞),
        ee v (𝒮.κ v (F.map (algebraMap 𝓞 (ZMod p))) ⊗ₜ[ZMod p] (1 : 𝒮.Ge v)) =
          (1 : ZMod p) ⊗ₜ[𝓞] Ψ v F) ∧
      (∀ v (y : 𝒮.Et v),
        ee v ((1 : 𝒮.Gc v) ⊗ₜ[ZMod p] 𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] y)) = (1 : ZMod p) ⊗ₜ[𝓞] ι v y) ∧
      (∀ v, (ee v).comp (Bialgebra.TensorProduct.map (𝒮.sc v) (𝒮.se v)) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)).comp (ee (v + 1))) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.solution
