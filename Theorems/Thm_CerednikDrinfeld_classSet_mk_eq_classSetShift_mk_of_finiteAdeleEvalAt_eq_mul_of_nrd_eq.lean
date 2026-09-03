import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_classSet_mk_eq_classSetShift_mk_of_finiteAdeleEvalAt_eq_mul_of_nrd_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra open CerednikDrinfeld hiding classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul classSetShift_mk_of_conjByFiniteIdele_eq mem_primeHeckeSet_of_nrd_eq_of_forall_finiteAdeleEvalAt_eq

theorem CerednikDrinfeld.classSet_mk_eq_classSetShift_mk_of_finiteAdeleEvalAt_eq_mul_of_nrd_eq
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
    (hq'N : ¬ q' ∣ N)
    (wbar : (ℍ[ℚ, a, b])ˣ)
    (hwbar : (nrd (wbar : ℍ[ℚ, a, b]) = (q' : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u wbar ∈ Submodule.localBoxUnits R u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ∀ x : CosetGraph.Loc a b u,
          ((((CosetGraph.toLoc u wbar)⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * x *
              ((CosetGraph.toLoc u wbar : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) ∈ Submodule.localBox R u ↔
            x ∈ Submodule.localBox R u) ∧
          ((((CosetGraph.toLoc u wbar)⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * x *
              ((CosetGraph.toLoc u wbar : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) ∈ Submodule.localBox Λ u ↔
            x ∈ Submodule.localBox Λ u))))
    (ϖ' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hϖ'supp : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (ϖ' : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hϖ'T : ϖ' ∈ primeHeckeSet (meetOrder R n) q')
    (hϖ'norm : Submodule.conjByFiniteIdele (meetOrder R n) ϖ' = meetOrder R n)
    (hϖ'sq : ∃ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n),
      ϖ' * ϖ' = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q'.Prime).ne_zero))) * u)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hy : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hyv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] wbar : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) y =
      classSetShift (Submodule.finiteIdeleStabilizer (meetOrder R n)) ϖ'
        (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_classSet_mk_eq_classSetShift_mk_of_finiteAdeleEvalAt_eq_mul_of_nrd_eq.solution
