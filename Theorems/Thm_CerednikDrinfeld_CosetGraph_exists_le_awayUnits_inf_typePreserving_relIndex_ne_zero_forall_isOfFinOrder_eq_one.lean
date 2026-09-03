import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open scoped TensorProduct Quaternion MatrixGroups
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld ValuationSubring

theorem CerednikDrinfeld.CosetGraph.exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ratClosure A)] [IsFractionRing R₀ ↥(ratClosure A)]
    (hR₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ratClosure A)))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x))
    [MulAction (ℍ[ℚ, a, b])ˣ (LT.LatticeTree.Vertex R₀ ↥(ratClosure A))] :
    ∃ Γ'' : Subgroup (ℍ[ℚ, a, b])ˣ,
      Γ'' ≤ CosetGraph.awayUnits R v ⊓ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
          (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A)) ∧
      Γ''.relIndex (CosetGraph.awayUnits R v ⊓ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
          (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A))) ≠ 0 ∧
      ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one.solution
