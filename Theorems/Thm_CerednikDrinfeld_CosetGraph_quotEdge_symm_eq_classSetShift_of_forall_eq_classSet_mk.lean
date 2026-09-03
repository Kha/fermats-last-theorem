import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_quotEdge_symm_eq_classSetShift_of_forall_eq_classSet_mk
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra open CerednikDrinfeld hiding classSetShift_mk_of_conjByFiniteIdele_eq

theorem CerednikDrinfeld.CosetGraph.quotEdge_symm_eq_classSetShift_of_forall_eq_classSet_mk
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hq5 : 5 ≤ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (N : ℕ) [NeZero N] (hN : Squarefree N) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (r : ℕ) [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R r)
    (hS : IsEichlerOrder (meetOrder R n) (N * r))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (eE : Mumford.QuotEdge (CosetGraph.ProjAwayUnits R v)
          (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)) ≃
          ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))
    (heE : (∀ (d : (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart)
          (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
          (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
            Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) →
          d.fst = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom x : (CosetGraph.Loc a b v)ˣ) :
            CosetGraph.Vert R v) →
          d.snd = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom x *
            Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n : (CosetGraph.Loc a b v)ˣ) :
              CosetGraph.Vert R v) →
          eE (Quotient.mk (MulAction.orbitRel (CosetGraph.ProjAwayUnits R v)
            (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart) d) =
            ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) x))
    (d : (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart) :
    eE (Quotient.mk (MulAction.orbitRel (CosetGraph.ProjAwayUnits R v)
        (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart) d.symm) =
      classSetShift (Submodule.finiteIdeleStabilizer (meetOrder R n)) n
        (eE (Quotient.mk (MulAction.orbitRel (CosetGraph.ProjAwayUnits R v)
          (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart) d)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_quotEdge_symm_eq_classSetShift_of_forall_eq_classSet_mk.solution
