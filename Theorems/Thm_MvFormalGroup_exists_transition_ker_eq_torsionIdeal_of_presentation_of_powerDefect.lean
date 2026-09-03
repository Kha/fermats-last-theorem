import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_transition_ker_eq_torsionIdeal_of_presentation_of_powerDefect

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u

theorem MvFormalGroup.exists_transition_ker_eq_torsionIdeal_of_presentation_of_powerDefect
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)

    (he : ℕ) (E : ℕ → Type u) [∀ v, CommRing (E v)] [∀ v, HopfAlgebra 𝓞 (E v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (E v)] [∀ v, Module.Free 𝓞 (E v)] [∀ v, Module.Finite 𝓞 (E v)]
    (st : ∀ v, E (v + 1) →ₐc[𝓞] E v) (hst : ∀ v, Function.Surjective (st v))
    (hrankE : ∀ v, Module.finrank 𝓞 (E v) = p ^ (v * he))
    (hkerE : ∀ v, RingHom.ker (st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (E (v + 1)) (p ^ v))

    (c₂ : ∀ v, Fin d → E v ⊗[𝓞] E v)
    (hc₂st : ∀ v i, Algebra.TensorProduct.map (st v : E (v + 1) →ₐ[𝓞] E v)
        (st v : E (v + 1) →ₐ[𝓞] E v) (c₂ (v + 1) i) = c₂ v i)
    (hc₂p : ∀ v i, c₂ v i ∈ Ideal.span {(p : E v ⊗[𝓞] E v)})

    (C : ∀ v, ℕ → Fin d → E v)
    (hCp : ∀ v n i, C v n i ∈ Ideal.span {(p : E v)})
    (hCcounit : ∀ v n i, Coalgebra.counit (R := 𝓞) (C v n i) = 0)
    (hCst : ∀ v n i, st v (C (v + 1) n i) = C v n i)
    (hCper : ∀ v m i, C v (p ^ v * m) i =
      MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.nthSeries m i))

    (L : ℕ → Type u) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (ι : ∀ v, E v →ₐc[𝓞] L v) (Ψ : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L v)
    (θ : ∀ v, MvPowerSeries (Fin d) (E v) →ₐ[𝓞] L v)
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h) * Module.finrank 𝓞 (E v))
    (hθs : ∀ v, Function.Surjective (θ v))
    (hθC : ∀ v (e : E v), θ v (MvPowerSeries.C e) = ι v e)
    (hθX : ∀ v i, θ v (X i) = Ψ v (X i))
    (hθker : ∀ v, RingHom.ker (θ v) =
      Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 (E v)) -
        MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.invSeries i))))
    (hΨrad : ∀ v i, Ψ v (X i) ∈ (Ideal.span {(p : L v)}).radical)
    (hΨeval : ∀ v F, Ψ v F = MvFormalGroup.adicEval (Ideal.span {(p : L v)}) (fun i => Ψ v (X i)) F)
    (hΨcounit : ∀ v i, Coalgebra.counit (R := 𝓞) (Ψ v (X i)) = 0)
    (hgen : ∀ v, Function.Surjective
      (Algebra.TensorProduct.lift (ι v : E v →ₐ[𝓞] L v) (Ψ v) (fun _ _ => Commute.all _ _)))
    (hcomul : ∀ v i, Coalgebra.comul (R := 𝓞) (Ψ v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
        (Sum.elim (fun j => Ψ v (X j) ⊗ₜ[𝓞] (1 : L v))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
            (Sum.elim (fun j => (1 : L v) ⊗ₜ[𝓞] Ψ v (X j))
              (fun j => Algebra.TensorProduct.map (ι v : E v →ₐ[𝓞] L v) (ι v : E v →ₐ[𝓞] L v) (c₂ v j)))
            (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i))
    (hnsmul : ∀ v n i, PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) n (Ψ v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L v)})
        (Sum.elim (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L v)}) (fun k => Ψ v (X k)) (Φ.nthSeries n j))
          (fun j => ι v (C v n j)))
        (Φ.toPowerSeries i)) :
    ∃ t : ∀ v, L (v + 1) →ₐc[𝓞] L v,
      (∀ v, Function.Surjective (t v)) ∧
      (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * (h + he))) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
      (∀ v, (t v).comp (ι (v + 1)) = (ι v).comp (st v)) ∧
      (∀ v, ((t v : L (v + 1) →ₐc[𝓞] L v) : L (v + 1) →ₐ[𝓞] L v).comp (Ψ (v + 1)) = Ψ v) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_transition_ker_eq_torsionIdeal_of_presentation_of_powerDefect.solution
