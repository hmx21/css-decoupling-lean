import Decoupling.HighDim.AlgorithmTwoPipelineCocycles

/-!
# Native existence and completeness for the stored-layer comparison

Only proposition proofs use the original formal witness. The target
multiplicities and cocycles are the stored outputs of the executed
cohomology stage, and every map with those values is a quasi-isomorphism.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex AlgorithmTwoCohomology AlgorithmTwoComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)
noncomputable section

omit [DecidableEq K] in
private theorem result_cycle_transport {q B : ℕ} (r₁ r₂ : Result K D q B) (he : r₁=r₂)
    (i : Fin r₁.dimension) :
    r₁.cycle i = r₂.cycle (Fin.cast (congrArg Result.dimension he) i) := by subst r₂; rfl

theorem storedMultiplicity_correct (s : InputLayers cC inp hDL) :
    AlgorithmTwoToricData.multiplicities D s.multiplicities =
      AlgorithmTwoComputedLayers.outputMultiplicities cC (incoming cC inp hDL) (outgoing cC inp hDL) := by
  funext j
  exact s.multiplicities_correct j

theorem nativeStoredCycle_correct (s : InputLayers cC inp hDL)
    (i : AlgorithmTwoToricData.Copy D s.multiplicities) :
    nativeStoredCycle cC inp hDL s i =
      AlgorithmTwoComputedLayers.outputCycle cC (incoming cC inp hDL) (outgoing cC inp hDL)
        i.1 (Fin.cast (s.multiplicities_correct i.1) i.2) := by
  change (cC.equiv (i.1.val+1)).symm ((s.result i.1).cycle _) =
    (cC.equiv (i.1.val+1)).symm ((AlgorithmTwoComputedLayers.output cC
      (incoming cC inp hDL) (outgoing cC inp hDL) i.1).cycle _)
  rw [result_cycle_transport _ _ (s.result_correct i.1)]
  congr 2

private theorem comparison_exists_of_counts (t : Fin (D-1) → ℕ)
    (ht : t=AlgorithmTwoComputedLayers.outputMultiplicities cC (incoming cC inp hDL) (outgoing cC inp hDL))
    (cycle : ∀ i : Toric.Copies D t, C.X (i.1.val+1))
    (hcycle : ∀ (j : Fin (D-1)) (k : Fin (t j)), cycle ⟨j,k⟩ =
      AlgorithmTwoComputedLayers.outputCycle cC (incoming cC inp hDL) (outgoing cC inp hDL) j
        (Fin.cast (congrFun ht j) k)) :
    ∃ g : Toric.stackModel K D (Toric.copyForms D t) ⟶ C, QuasiIso g ∧
      ∀ i : Toric.Copies D t, g.f (i.1.val+1) (stackTop K D (Toric.copyForms D t) i) = cycle i := by
  subst t
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  obtain ⟨g,hg,htop⟩ := AlgorithmTwoComputedLayers.program_comparison_exists cC old e
    (incoming cC inp hDL) (outgoing cC inp hDL) (incoming_action cC inp hDL) (outgoing_action cC inp hDL)
  refine ⟨g,hg,?_⟩
  rintro ⟨j,k⟩
  rw [htop,hcycle]
  rfl

private theorem comparison_quasiIso_of_counts (t : Fin (D-1) → ℕ)
    (ht : t=AlgorithmTwoComputedLayers.outputMultiplicities cC (incoming cC inp hDL) (outgoing cC inp hDL))
    (cycle : ∀ i : Toric.Copies D t, C.X (i.1.val+1))
    (hcycle : ∀ (j : Fin (D-1)) (k : Fin (t j)), cycle ⟨j,k⟩ =
      AlgorithmTwoComputedLayers.outputCycle cC (incoming cC inp hDL) (outgoing cC inp hDL) j
        (Fin.cast (congrFun ht j) k))
    (g : Toric.stackModel K D (Toric.copyForms D t) ⟶ C)
    (hg : ∀ i : Toric.Copies D t, g.f (i.1.val+1) (stackTop K D (Toric.copyForms D t) i) = cycle i) :
    QuasiIso g := by
  subst t
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  apply AlgorithmTwoComputedLayers.program_solution_quasiIso cC old e
    (incoming cC inp hDL) (outgoing cC inp hDL) (incoming_action cC inp hDL) (outgoing_action cC inp hDL) g
  intro j k
  rw [hg ⟨j,k⟩,hcycle]
  rfl

theorem stored_comparison_exists (s : InputLayers cC inp hDL) :
    ∃ g : AlgorithmTwoToricData.nativeStack D s.multiplicities K ⟶ C, QuasiIso g ∧
      ∀ i : AlgorithmTwoToricData.Copy D s.multiplicities,
        g.f (i.1.val+1) (stackTop K D (Toric.copyForms D (AlgorithmTwoToricData.multiplicities D s.multiplicities)) i) =
          nativeStoredCycle cC inp hDL s i :=
  comparison_exists_of_counts cC inp hDL _ (storedMultiplicity_correct cC inp hDL s)
    (nativeStoredCycle cC inp hDL s) (fun j k => nativeStoredCycle_correct cC inp hDL s ⟨j,k⟩)

theorem stored_solution_quasiIso (s : InputLayers cC inp hDL)
    (g : AlgorithmTwoToricData.nativeStack D s.multiplicities K ⟶ C)
    (hg : ∀ i : AlgorithmTwoToricData.Copy D s.multiplicities,
        g.f (i.1.val+1) (stackTop K D (Toric.copyForms D (AlgorithmTwoToricData.multiplicities D s.multiplicities)) i) =
          nativeStoredCycle cC inp hDL s i) : QuasiIso g :=
  comparison_quasiIso_of_counts cC inp hDL _ (storedMultiplicity_correct cC inp hDL s)
    (nativeStoredCycle cC inp hDL s) (fun j k => nativeStoredCycle_correct cC inp hDL s ⟨j,k⟩) g hg

end
end Decoupling.HighDim.AlgorithmTwoPipeline
