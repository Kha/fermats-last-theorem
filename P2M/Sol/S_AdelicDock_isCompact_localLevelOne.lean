import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
namespace P2MW.S_AdelicDock_isCompact_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem solution
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    (v : HeightOneSpectrum R) (N : Ideal R) :
    IsCompact (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
  classical
  set C : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    {m | AdelicDock.IsLocalLevelOne R K v N m} with hC_def

  haveI : CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have hO : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hpi : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO

  have hCcl : IsClosed C := by
    have h1 : IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) |
        ∀ i j, m i j ∈ v.adicCompletionIntegers K} := by
      have : {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | ∀ i j, m i j ∈ v.adicCompletionIntegers K}
          = ⋂ i, ⋂ j, (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m i j) ⁻¹'
              (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
        ext m; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        (Valued.isClosed_valuationSubring (v.adicCompletion K)).preimage (continuous_id.matrix_elem i j)
    have h2 : IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) |
        Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v} :=
      (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := K) v N).preimage (continuous_id.matrix_elem 1 0)
    have h3 : IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) |
        Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v} :=
      (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := K) v N).preimage
        ((continuous_id.matrix_elem 1 1).sub continuous_const)
    have hCeq : C = ({m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | ∀ i j, m i j ∈ v.adicCompletionIntegers K}
        ∩ {m | Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v})
        ∩ {m | Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v} := by
      ext m
      simp only [hC_def, Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
    rw [hCeq]
    exact (h1.inter h2).inter h3
  have hC : IsCompact C :=
    hpi.of_isClosed_subset hCcl fun m hm i _ j _ => hm.integral i j

  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K)))
      = (Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹' (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
    simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image, hC_def, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
    · rintro ⟨h1, m, hm, hm'⟩
      refine ⟨h1, ?_⟩
      have : m = ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        MulOpposite.op_injective hm'
      rw [← this]; exact hm
  rw [heq]; exact hK
