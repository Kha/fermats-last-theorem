import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_ratClosure_smul_eq_and_natCard_stabilizer_mapDart_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open scoped TensorProduct Quaternion MatrixGroups
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld open ValuationSubring hiding exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime

theorem CerednikDrinfeld.CosetGraph.exists_iso_tree_ratClosure_smul_eq_and_natCard_stabilizer_mapDart_eq
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ primeHeckeSet R r)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ratClosure A)] [IsFractionRing R₀ ↥(ratClosure A)]
    (hR₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ratClosure A)))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x)) :
    ∃ (e : CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n) ≃g
        BruhatTits.tree R₀ ↥(ratClosure A))
      (ψ : CosetGraph.ProjAwayUnits R v ≃* ↥((CosetGraph.awayUnits R v).map ρ)),

      (∀ (g : (ℍ[ℚ, a, b])ˣ) (y : (CosetGraph.Loc a b v)ˣ),
        e ((CosetGraph.toLoc v g * y : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) =
          ρ g • e ((y : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v)) ∧

      (∀ γ : ↥(CosetGraph.awayUnits R v),
        ((ψ (QuotientGroup.mk γ : CosetGraph.ProjAwayUnits R v) : ↥((CosetGraph.awayUnits R v).map ρ)) :
          PGL(2, ↥(ratClosure A))) = ρ (γ : (ℍ[ℚ, a, b])ˣ)) ∧
      (∀ (γ : CosetGraph.ProjAwayUnits R v) (x : CosetGraph.Vert R v), e (γ • x) = ψ γ • e x) ∧

      (∀ d : (CosetGraph.graph R v
          (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart,
        Nat.card ↥(MulAction.stabilizer ↥((CosetGraph.awayUnits R v).map ρ) (e.toEmbedding.toHom.mapDart d)) =
          Nat.card ↥(MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) d)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_ratClosure_smul_eq_and_natCard_stabilizer_mapDart_eq.solution
