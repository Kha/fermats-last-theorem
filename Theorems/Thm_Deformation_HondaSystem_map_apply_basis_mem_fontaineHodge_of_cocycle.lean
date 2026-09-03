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
import P2M.Sol.S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem Deformation.HondaSystem.map_apply_basis_mem_fontaineHodge_of_cocycle
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (h𝒮 : 𝒮.Lawful)
    (Φ : MvFormalGroup 𝒮.d 𝓞) [Φ.IsComm]
    (c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
    (hc₂p : ∀ v i, c₂ v i ∈ Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)})
    (hLOGA :
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (x x' : Fin 𝒮.d → g),
          (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, x' j ∈ (Ideal.span {(p : g)}).radical) → ∀ i : Fin 𝒮.d,
          Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)})
              (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x) ((fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x') ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) (Φ.toPowerSeries i)) (𝒮.a i n)) +
            Deformation.PLoc.wSeries p (fun k => ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (𝒮.ĉ i k v)) =
          (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f (𝒮.ĉ i k v))) +
            (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x' (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f' (𝒮.ĉ i k v)))))

    (v : ℕ) (Lv : Type u) [CommRing Lv] [HopfAlgebra 𝓞 Lv] [Module.Free 𝓞 Lv] [Module.Finite 𝓞 Lv]
    (ιv : 𝒮.Et v →ₐc[𝓞] Lv) (Ψv : MvPowerSeries (Fin 𝒮.d) 𝓞 →ₐ[𝓞] Lv)
    (hΨrad : ∀ i, Ψv (X i) ∈ (Ideal.span {(p : Lv)}).radical)
    (hΨeval : ∀ F, Ψv F = MvFormalGroup.adicEval (Ideal.span {(p : Lv)}) (fun i => Ψv (X i)) F)
    (hΨε : ∀ i, Coalgebra.counit (R := 𝓞) (Ψv (X i)) = 0)
    (hcomul : ∀ i, Coalgebra.comul (R := 𝓞) (Ψv (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)})
          (Sum.elim (fun j => Ψv (X j) ⊗ₜ[𝓞] (1 : Lv))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)})
              (Sum.elim (fun j => (1 : Lv) ⊗ₜ[𝓞] Ψv (X j))
                (fun j => Algebra.TensorProduct.map (ιv : 𝒮.Et v →ₐ[𝓞] Lv) (ιv : 𝒮.Et v →ₐ[𝓞] Lv)
                  (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i))
    (hkill : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 Lv (p ^ v) =
        (Algebra.ofId 𝓞 Lv).comp (Bialgebra.counitAlgHom 𝓞 Lv))

    (ee : 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐc[ZMod p] ZMod p ⊗[𝓞] Lv)
    (heeκ : ∀ F : MvPowerSeries (Fin 𝒮.d) 𝓞,
        ee (𝒮.κ v (F.map (algebraMap 𝓞 (ZMod p))) ⊗ₜ[ZMod p] (1 : 𝒮.Ge v)) = (1 : ZMod p) ⊗ₜ[𝓞] Ψv F)
    (heeθ : ∀ y : 𝒮.Et v,
        ee ((1 : 𝒮.Gc v) ⊗ₜ[ZMod p] 𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] y)) = (1 : ZMod p) ⊗ₜ[𝓞] ιv y)
    (i : Fin 𝒮.d) :
    Deformation.DieudonneModule.map (ZMod p) p
        ((ee.comp (𝒮.Θ v)) : G v →ₐc[ZMod p] ZMod p ⊗[𝓞] Lv)
        (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞)) ∈
      Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : Lv →ₐ[𝓞] ZMod p ⊗[𝓞] Lv).toRingHom := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle.solution
