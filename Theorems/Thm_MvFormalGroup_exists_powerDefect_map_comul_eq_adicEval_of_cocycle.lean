import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u

theorem MvFormalGroup.exists_powerDefect_map_comul_eq_adicEval_of_cocycle
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]

    (E : ℕ → Type u) [∀ v, CommRing (E v)] [∀ v, HopfAlgebra 𝓞 (E v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (E v)] [∀ v, Module.Free 𝓞 (E v)] [∀ v, Module.Finite 𝓞 (E v)]
    (st : ∀ v, E (v + 1) →ₐc[𝓞] E v) (hst : ∀ v, Function.Surjective (st v))
    (hkerE : ∀ v, RingHom.ker (st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (E (v + 1)) (p ^ v))

    (c₂ : ∀ v, Fin d → E v ⊗[𝓞] E v)
    (hCOC :
      (∀ v i, Algebra.TensorProduct.map (st v : E (v + 1) →ₐ[𝓞] E v)
          (st v : E (v + 1) →ₐ[𝓞] E v) (c₂ (v + 1) i) = c₂ v i) ∧
      (∀ v i, c₂ v i ∈ Ideal.span {(p : E v ⊗[𝓞] E v)}) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f : E v →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (E v))) (fun _ _ => Commute.all _ _) (c₂ v j) = 0 ∧
          Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (E v))) f (fun _ _ => Commute.all _ _) (c₂ v j) = 0) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : E v →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j) = Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ v j)) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' f'' : E v →ₐ[𝓞] g),
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (E v))) f'' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)) =
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (E v))) (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) :
    ∃ C : ∀ v, ℕ → Fin d → E v,

      (∀ v i, C v 0 i = 0) ∧
      (∀ v n i, C v (n + 1) i =
        MvFormalGroup.adicEval (Ideal.span {(p : E v)})
          (Sum.elim (C v n) (fun j => Algebra.TensorProduct.lmul' 𝓞 (S := E v)
            (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n) (AlgHom.id 𝓞 (E v))
              (c₂ v j))))
          (Φ.toPowerSeries i)) ∧

      (∀ v n i, C v n i ∈ Ideal.span {(p : E v)}) ∧
      (∀ v n i, Coalgebra.counit (R := 𝓞) (C v n i) = 0) ∧

      (∀ v n i, st v (C (v + 1) n i) = C v n i) ∧
      (∀ v m i, C v (p ^ v * m) i =
        MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.nthSeries m i)) ∧

      (∀ v n i,
        MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
          (Sum.elim (fun j => Coalgebra.comul (R := 𝓞) (C v n j))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)}) (c₂ v) (Φ.nthSeries n j)))
          (Φ.toPowerSeries i) =
        MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
          (Sum.elim (fun j => C v n j ⊗ₜ[𝓞] (1 : E v))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
              (Sum.elim (fun j => (1 : E v) ⊗ₜ[𝓞] C v n j)
                (fun j => Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n)
                  (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n) (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle.solution
