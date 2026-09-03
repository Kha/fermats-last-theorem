import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeOrbital
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem
LT.LatticeTree.unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u)
    (Tc : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hTc : ∀ t : GL (Fin 2) (v.adicCompletion K),
      t ∈ Tc ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        ∃ w : (v.adicCompletionIntegers K)ˣ,
          Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w)
    (St : GL (Fin 2) (v.adicCompletion K) → Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hSt : ∀ s t : GL (Fin 2) (v.adicCompletion K),
      t ∈ St s ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        s⁻¹ * t * s ∈ AutomorphicForm.localIntegralSet K v)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hSsupp : ∀ s ∈ S, s⁻¹ * γ * s ∈ AutomorphicForm.localIntegralSet K v)
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K), x⁻¹ * γ * x ∈ AutomorphicForm.localIntegralSet K v →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ =
      (Tc ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S, (St s).relIndex Tc := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap.solution
