import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ primeHeckeSet R r)
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (d : (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart)
    (hd₁ : d.fst = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom z :
      (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v))
    (hd₂ : d.snd = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom z *
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n : (CosetGraph.Loc a b v)ˣ) :
        CosetGraph.Vert R v)) :
    Finite (MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) d) ∧
      Nat.card (MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) d) =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) z) u} / 2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two.solution
