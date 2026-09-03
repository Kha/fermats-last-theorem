import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u

theorem MvFormalGroup.exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)
    (hh : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p))) =
      p ^ h)

    (E : Type u) [CommRing E] [HopfAlgebra 𝓞 E] [Coalgebra.IsCocomm 𝓞 E] [Module.Free 𝓞 E] [Module.Finite 𝓞 E]
    (v : ℕ)
    (hkill : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 E (p ^ v) =
      (Algebra.ofId 𝓞 E).comp (Bialgebra.counitAlgHom 𝓞 E))

    (c₂ : Fin d → E ⊗[𝓞] E)
    (hc₂p : ∀ i, c₂ i ∈ Ideal.span {(p : E ⊗[𝓞] E)})
    (hc₂unit : (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (f : E →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 E)) (fun _ _ => Commute.all _ _) (c₂ j) = 0 ∧
          Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 E)) f (fun _ _ => Commute.all _ _) (c₂ j) = 0))
    (hc₂symm : (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (f f' : E →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ j) = Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ j)))
    (hc₂coc : (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (f f' f'' : E →ₐ[𝓞] g),
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 E)) f'' (fun _ _ => Commute.all _ _) (c₂ j)))) (Φ.toPowerSeries i)) =
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 E)) (fun _ _ => Commute.all _ _) (c₂ j)))) (Φ.toPowerSeries i))))

    (C : ℕ → Fin d → E)
    (hC0 : ∀ i, C 0 i = 0)
    (hCsucc : ∀ n i, C (n + 1) i =
      MvFormalGroup.adicEval (Ideal.span {(p : E)})
        (Sum.elim (C n) (fun j => Algebra.TensorProduct.lmul' 𝓞 (S := E)
          (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 E n) (AlgHom.id 𝓞 E) (c₂ j))))
        (Φ.toPowerSeries i))
    (hCp : ∀ n i, C n i ∈ Ideal.span {(p : E)})
    (hCcounit : ∀ n i, Coalgebra.counit (R := 𝓞) (C n i) = 0)
    (hCprod : ∀ n i,
      MvFormalGroup.adicEval (Ideal.span {(p : E ⊗[𝓞] E)})
        (Sum.elim (fun j => Coalgebra.comul (R := 𝓞) (C n j))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E ⊗[𝓞] E)}) c₂ (Φ.nthSeries n j)))
        (Φ.toPowerSeries i) =
      MvFormalGroup.adicEval (Ideal.span {(p : E ⊗[𝓞] E)})
        (Sum.elim (fun j => C n j ⊗ₜ[𝓞] (1 : E))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E ⊗[𝓞] E)})
            (Sum.elim (fun j => (1 : E) ⊗ₜ[𝓞] C n j)
              (fun j => Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 E n)
                (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 E n) (c₂ j)))
            (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i)) :
    ∃ (Lv : Type u) (_ : CommRing Lv) (_ : HopfAlgebra 𝓞 Lv) (_ : Coalgebra.IsCocomm 𝓞 Lv)
      (_ : Module.Free 𝓞 Lv) (_ : Module.Finite 𝓞 Lv)
      (ι : E →ₐc[𝓞] Lv) (Ψ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] Lv) (θ : MvPowerSeries (Fin d) E →ₐ[𝓞] Lv),

      Module.finrank 𝓞 Lv = p ^ (v * h) * Module.finrank 𝓞 E ∧

      Function.Surjective θ ∧
      (∀ e : E, θ (MvPowerSeries.C e) = ι e) ∧
      (∀ i, θ (X i) = Ψ (X i)) ∧
      RingHom.ker θ = Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E) -
        MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E)}) (C (p ^ v)) (Φ.invSeries i))) ∧

      (∀ i, Ψ (X i) ∈ (Ideal.span {(p : Lv)}).radical) ∧
      (∀ F, Ψ F = MvFormalGroup.adicEval (Ideal.span {(p : Lv)}) (fun i => Ψ (X i)) F) ∧
      (∀ i, Coalgebra.counit (R := 𝓞) (Ψ (X i)) = 0) ∧
      (∀ i, Ψ (Φ.nthSeries (p ^ v) i) ∈ Ideal.span {(p : Lv)}) ∧
      Function.Surjective (Algebra.TensorProduct.lift (ι : E →ₐ[𝓞] Lv) Ψ (fun _ _ => Commute.all _ _)) ∧

      (∀ i, Coalgebra.comul (R := 𝓞) (Ψ (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)})
          (Sum.elim (fun j => Ψ (X j) ⊗ₜ[𝓞] (1 : Lv))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)})
              (Sum.elim (fun j => (1 : Lv) ⊗ₜ[𝓞] Ψ (X j))
                (fun j => Algebra.TensorProduct.map (ι : E →ₐ[𝓞] Lv) (ι : E →ₐ[𝓞] Lv) (c₂ j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i)) ∧
      (∀ n i, PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 Lv n (Ψ (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : Lv)})
          (Sum.elim (fun j => MvFormalGroup.adicEval (Ideal.span {(p : Lv)}) (fun k => Ψ (X k)) (Φ.nthSeries n j))
            (fun j => ι (C n j)))
          (Φ.toPowerSeries i)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect.solution
