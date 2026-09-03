import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_padicValRat_nrd
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open CerednikDrinfeld LT.LatticeTree QuaternionAlgebra open ValuationSubring hiding isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime

theorem CerednikDrinfeld.BruhatTits.mem_typePreserving_iff_even_padicValRat_nrd
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ratClosure A)] [IsFractionRing R₀ ↥(ratClosure A)]
    (hR₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ratClosure A)))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x))
    [MulAction (ℍ[ℚ, a, b])ˣ (LT.LatticeTree.Vertex R₀ ↥(ratClosure A))]
    (hact : ∀ (g : (ℍ[ℚ, a, b])ˣ) (x : LT.LatticeTree.Vertex R₀ ↥(ratClosure A)), g • x = ρ g • x)
    (x : (ℍ[ℚ, a, b])ˣ) :
    x ∈ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
        (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A)) ↔
      Even (padicValRat r (nrd (x : ℍ[ℚ, a, b]))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_padicValRat_nrd.solution
