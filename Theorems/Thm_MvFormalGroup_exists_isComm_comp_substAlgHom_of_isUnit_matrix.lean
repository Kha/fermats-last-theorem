import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_isComm_comp_substAlgHom_of_isUnit_matrix

open scoped TensorProduct
open MvPowerSeries

universe v

theorem MvFormalGroup.exists_isComm_comp_substAlgHom_of_isUnit_matrix
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (Φ : MvFormalGroup d (ZMod p)) [Φ.IsComm]
    (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v)
    (hκsurj : ∀ v, Function.Surjective (κ v))
    (hκker : ∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v))))
    (hκs : ∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ (v + 1)) = κ v)
    (hκε : ∀ v i, Coalgebra.counit (R := ZMod p) (κ v (X i)) = 0)
    (hκrad : ∀ v i, κ v (X i) ∈ (Ideal.span {(p : G v)}).radical)
    (hκeval : ∀ v F, κ v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ v (X i)) F)
    (hκΔ : ∀ v i, Coalgebra.comul (R := ZMod p) (κ v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
        (Sum.elim (fun j => κ v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ v (X j)))
        (Φ.toPowerSeries i))
    (P : Matrix (Fin d) (Fin d) (ZMod p)) (hP : IsUnit P) :
    ∃ (Φ' : MvFormalGroup d (ZMod p)) (_ : Φ'.IsComm) (ℓ : MvFormalGroup.Hom Φ Φ')
      (κ' : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v),
      (ℓ.toPowerSeries = fun i => ∑ j, P i j • (X j : MvPowerSeries (Fin d) (ZMod p))) ∧
      (∀ v F, κ' v F = κ v (MvPowerSeries.subst ℓ.toPowerSeries F)) ∧
      (∀ v, Function.Surjective (κ' v)) ∧
      (∀ v, RingHom.ker (κ' v) = Ideal.span (Set.range (Φ'.nthSeries (p ^ v)))) ∧
      (∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ' (v + 1)) = κ' v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (κ' v (X i)) = 0) ∧
      (∀ v i, κ' v (X i) ∈ (Ideal.span {(p : G v)}).radical) ∧
      (∀ v F, κ' v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ' v (X i)) F) ∧
      (∀ v i, Coalgebra.comul (R := ZMod p) (κ' v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
          (Sum.elim (fun j => κ' v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ' v (X j)))
          (Φ'.toPowerSeries i)) ∧
      Module.finrank (ZMod p) (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ'.nthSeries p))) =
        Module.finrank (ZMod p) (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_isComm_comp_substAlgHom_of_isUnit_matrix.solution
