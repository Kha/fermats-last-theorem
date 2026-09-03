import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
attribute [-instance] PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule
attribute [-simp] PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct in

theorem PDivisibleGroup.CartierDuality.linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n)
    (b : Module.Basis (Fin n) (PadicAlgCl.ringOfIntegers p K) G.cotangentModule)
    (dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]))
    (hdα : ∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ)
        (ψ : G'.Point (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v),
        G'.pointsMkAdd (PadicAlgCl p) v
            (Additive.ofMul (G'.pointMap
              (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).val v ψ)) =
          (y : ℕ → G'.Points (PadicAlgCl p)) v →
        ∀ z : integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)
            ⊗[PadicAlgCl.ringOfIntegers p K] G.cotangentModule,
          (G.cotangentModuleProj v).lTensor
              (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z =
            D.charDiff (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v ψ →
          ‖dα j y - ((TensorProduct.rid (PadicAlgCl.ringOfIntegers p K)
              (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p))
              ((b.coord j).lTensor
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z) :
                PadicAlgCl p) : ℂ_[p])‖ ≤
            (p : ℝ) ^ (-(v : ℤ))) :
    LinearIndependent K
      (fun j => (⇑(dα j) : TateModule p (G'.Points (PadicAlgCl p)) → ℂ_[p])) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers.solution
