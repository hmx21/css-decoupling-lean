import Decoupling.HighDim.AlgorithmTwoToricDataIndex
import Decoupling.HighDim.AlgorithmTwoToricDataTermCoordinates
import Decoupling.HighDim.AlgorithmTwoFiniteComplexCoordinates
import Decoupling.HighDim.ToricStack
import Decoupling.HighDim.ToricSplitCircuit

/-!
# Actual toric-stack coordinates with the explicit total mask labels

The total coordinate array uses the computable copy-mask enumeration.
The native equivalence is proved from the actual Koszul terms and
the actual finite biproduct. It supplies no differential or splitting
as a coordinate assumption.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
noncomputable section
variable (D : ℕ) (t : Vector ℕ (D - 1))

def gradeLabelEquiv (n : ℤ) :
    (Σ c : Copy D t, GradeMask D ((c.1.val : ℤ) + 1) n) ≃
      {a : Fin (totalRank D t) // (degrees D t).get a = n} where
  toFun a := ⟨(labelEquiv D t).symm (a.1, a.2.val), by
    simp only [degrees_get, labelDegree, Equiv.apply_symm_apply]
    exact a.2.property⟩
  invFun a := ⟨(labelEquiv D t a.val).1, ⟨(labelEquiv D t a.val).2, by
    simpa only [degrees_get, labelDegree] using a.property⟩⟩
  left_inv a := by
    rcases a with ⟨c, m, hm⟩
    have hp := (labelEquiv D t).apply_symm_apply (c, m)
    apply Sigma.ext (congrArg Prod.fst hp)
    apply (Subtype.heq_iff_coe_eq (fun a => by
      change (((labelEquiv D t) ((labelEquiv D t).symm (c, m))).1.1.val : ℤ) + 1 -
        (subsetAt D a).card = n ↔ (c.1.val : ℤ) + 1 - (subsetAt D a).card = n
      rw [hp])).mpr
    exact congrArg Prod.snd hp
  right_inv a := by
    apply Subtype.ext
    exact (labelEquiv D t).symm_apply_apply a.val

variable (K : Type) [Field K]

local instance toricDataCoordinatesFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

abbrev nativeStack : CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  Toric.stackModel K D (Toric.copyForms D (multiplicities D t))

def stackGradeCoordinates (n : ℤ) :
    (nativeStack D t K).X n ≃ₗ[Laurent K D]
      ({a : Fin (totalRank D t) // (degrees D t).get a = n} → Laurent K D) :=
  (Toric.stackTermIso K D (Toric.copyForms D (multiplicities D t)) n).toLinearEquiv.trans
    ((LinearEquiv.piCongrRight (fun c : Copy D t =>
      individualCoordinates K D ((c.1.val : ℤ) + 1) n)).trans
      ((LinearEquiv.piCurry (Laurent K D)
        (fun (c : Copy D t) (_ : GradeMask D ((c.1.val : ℤ) + 1) n) => Laurent K D)).symm.trans
          (LinearEquiv.piCongrLeft' (Laurent K D) (fun _ => Laurent K D) (gradeLabelEquiv D t n))))

def totalEmbed (n : ℤ) : (nativeStack D t K).X n →ₗ[Laurent K D] (Fin (totalRank D t) → Laurent K D) where
  toFun x i := if hi : (degrees D t).get i = n then stackGradeCoordinates D t K n x ⟨i, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : (degrees D t).get i = n
    · simp only [hi, dite_true, map_add, Pi.add_apply]
    · simp only [hi, dite_false, Pi.add_apply, add_zero]
  map_smul' a x := by
    funext i
    by_cases hi : (degrees D t).get i = n
    · simp only [hi, dite_true, map_smul, Pi.smul_apply, RingHom.id_apply]
    · simp only [hi, dite_false, Pi.smul_apply, smul_zero]

def totalProject (n : ℤ) : (Fin (totalRank D t) → Laurent K D) →ₗ[Laurent K D] (nativeStack D t K).X n where
  toFun x := (stackGradeCoordinates D t K n).symm (fun i => x i.val)
  map_add' x y := by
    change (stackGradeCoordinates D t K n).symm ((fun i => x i.val) + (fun i => y i.val)) = _
    exact map_add _ _ _
  map_smul' a x := by
    change (stackGradeCoordinates D t K n).symm (a • (fun i => x i.val)) = _
    exact map_smul _ _ _

def totalCoordinates : AlgorithmTwoFiniteComplex.Coordinates (nativeStack D t K) (totalRank D t) where
  degree := degrees D t
  embed := totalEmbed D t K
  project := totalProject D t K
  project_embed n x := by
    apply (stackGradeCoordinates D t K n).injective
    change (stackGradeCoordinates D t K n) ((stackGradeCoordinates D t K n).symm
      (fun i => totalEmbed D t K n x i.val)) = _
    rw [LinearEquiv.apply_symm_apply]
    funext i
    change (if hi : (degrees D t).get i.val = n then
      stackGradeCoordinates D t K n x ⟨i.val, hi⟩ else 0) = _
    rw [dite_eq_left i.property]
  embed_project n x i := by
    change (if hi : (degrees D t).get i = n then
      stackGradeCoordinates D t K n ((stackGradeCoordinates D t K n).symm
        (fun a => x a.val)) ⟨i, hi⟩ else 0) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl

theorem stackGradeCoordinates_label (n : ℤ) (x : (nativeStack D t K).X n)
    (c : Copy D t) (a : GradeMask D ((c.1.val : ℤ) + 1) n) :
    stackGradeCoordinates D t K n x (gradeLabelEquiv D t n ⟨c, a⟩) =
      individualCoordinates K D ((c.1.val : ℤ) + 1) n
        ((CategoryTheory.Limits.biproduct.π
          (fun c : Copy D t => Toric.model K D ((c.1.val : ℤ) + 1)) c).f n x) a := by
  change ((LinearEquiv.piCurry (Laurent K D)
    (fun (c : Copy D t) (_ : GradeMask D ((c.1.val : ℤ) + 1) n) => Laurent K D)).symm
      (fun c => individualCoordinates K D ((c.1.val : ℤ) + 1) n
        ((Toric.stackTermIso K D (Toric.copyForms D (multiplicities D t)) n).hom x c)))
    ((gradeLabelEquiv D t n).symm ((gradeLabelEquiv D t n) ⟨c, a⟩)) = _
  rw [Equiv.symm_apply_apply]
  change individualCoordinates K D ((c.1.val : ℤ) + 1) n
    ((Toric.stackTermIso K D (Toric.copyForms D (multiplicities D t)) n).hom x c) a = _
  rw [Toric.stackTermIso_apply]
  dsimp +instances only [Toric.copyForms]

theorem totalEmbed_label (n : ℤ) (x : (nativeStack D t K).X n)
    (c : Copy D t) (m : Fin (2 ^ D)) (hm : (c.1.val : ℤ) + 1 - (subsetAt D m).card = n) :
    totalEmbed D t K n x ((labelEquiv D t).symm (c, m)) =
      individualCoordinates K D ((c.1.val : ℤ) + 1) n
        ((CategoryTheory.Limits.biproduct.π
          (fun c : Copy D t => Toric.model K D ((c.1.val : ℤ) + 1)) c).f n x) ⟨m, hm⟩ := by
  let a := gradeLabelEquiv D t n ⟨c, ⟨m, hm⟩⟩
  change totalEmbed D t K n x a.val = _
  change (if ha : (degrees D t).get a.val = n then stackGradeCoordinates D t K n x ⟨a.val, ha⟩ else 0) = _
  rw [dite_eq_left a.property]
  exact stackGradeCoordinates_label D t K n x c ⟨m, hm⟩

end
end Decoupling.HighDim.AlgorithmTwoToricData
