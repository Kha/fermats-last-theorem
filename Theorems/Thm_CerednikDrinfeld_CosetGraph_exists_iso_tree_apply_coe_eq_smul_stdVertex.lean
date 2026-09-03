import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex
attribute [-simp] LocalGL2.swapUnit_val LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open scoped TensorProduct Quaternion MatrixGroups
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_iso_tree_apply_coe_eq_smul_stdVertex
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    {r : ℕ} [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ t : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hφR : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ primeHeckeSet R r) :
    ∃ e : CosetGraph.graph R v
          (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n) ≃g
        BruhatTits.tree (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ),
      (∀ g : (CosetGraph.Loc a b v)ˣ,
        e ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) =
          (Units.map φ.toRingHom.toMonoidHom g : GL (Fin 2) (v.adicCompletion ℚ)) •
            LT.LatticeTree.stdVertex (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) ∧
      (∀ γ g : (CosetGraph.Loc a b v)ˣ,
        e ((γ * g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) =
          (Units.map φ.toRingHom.toMonoidHom γ : GL (Fin 2) (v.adicCompletion ℚ)) •
            e ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex.solution
