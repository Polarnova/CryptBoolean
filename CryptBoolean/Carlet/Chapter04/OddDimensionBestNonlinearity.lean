/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerDuality
public import CryptBoolean.Carlet.Chapter04.Nonlinearity
public import FABL.Chapter06.Constructions.BentFunctions

/-!
# Best nonlinearity in odd dimension

Explicit Kavut--Yücel and balanced Maitra--Kavut--Yücel functions, their
kernel-checked Walsh certificates, and their extensions by direct sums with
complete bent blocks.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The largest nonlinearity among Boolean functions in dimension `n`. -/
noncomputable def maximumNonlinearity (n : ℕ) : ℕ :=
  (Finset.univ : Finset (BooleanFunction n)).sup'
    Finset.univ_nonempty nonlinearity

/-- Every Boolean function is bounded by the maximum nonlinearity in its dimension. -/
theorem nonlinearity_le_maximumNonlinearity (f : BooleanFunction n) :
    nonlinearity f ≤ maximumNonlinearity n := by
  exact Finset.le_sup' nonlinearity (Finset.mem_univ f)

/-- The finite Boolean-function space contains a function attaining the
maximum nonlinearity. -/
theorem exists_nonlinearity_eq_maximumNonlinearity (n : ℕ) :
    ∃ f : BooleanFunction n, nonlinearity f = maximumNonlinearity n := by
  classical
  unfold maximumNonlinearity
  obtain ⟨f, _hf, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (BooleanFunction n)))
    Finset.univ_nonempty nonlinearity
  exact ⟨f, hmax.symm⟩

/-- Interpret a binary cube point as a little-endian natural number. -/
def f₂CubeNatIndex (x : FABL.F₂Cube n) : ℕ :=
  ∑ i, (x i).val * 2 ^ i.val

/-- Interpret the low `n` bits of a natural number as a binary cube point. -/
def f₂CubeOfNat (n k : ℕ) : FABL.F₂Cube n :=
  fun i ↦ if k.testBit i.val then 1 else 0

/-- Kavut--Yücel ePrint 2007/308, p. 6, first 512-bit truth table. -/
def kavutYucelTruthTable : ℕ :=
  0x68B7EF2DA03B0D3EA00DB6A96DD99AEAFDB9C842B6D5DC8C4526CE0DD29020DB * 2 ^ 256 +
    0xB75FE3314568344E73688FF0CB2482E065231869E1AA4583765CC491F8A8DB12

/-- The nine-variable function printed by Kavut and Yücel, with source bits
read left-to-right. -/
def kavutYucelFunction9 : BooleanFunction 9 :=
  fun x ↦ if kavutYucelTruthTable.testBit (511 - f₂CubeNatIndex x) then 1 else 0

private inductive WalshCertificateTree : ℕ → Type
  | leaf (value : ℤ) : WalshCertificateTree 0
  | branch {n : ℕ} (zero one : WalshCertificateTree n) :
      WalshCertificateTree (n + 1)

private def WalshCertificateTree.eval :
    {n : ℕ} → WalshCertificateTree n → FABL.F₂Cube n → ℤ
  | 0, .leaf value, _ => value
  | _ + 1, .branch zero one, a =>
      if a 0 = 0 then zero.eval (Fin.tail a) else one.eval (Fin.tail a)

private def WalshCertificateTree.butterfly :
    {n : ℕ} → WalshCertificateTree n → WalshCertificateTree n →
      WalshCertificateTree n × WalshCertificateTree n
  | 0, .leaf x, .leaf y => (.leaf (x + y), .leaf (x - y))
  | _ + 1, .branch x₀ x₁, .branch y₀ y₁ =>
      let zero := butterfly x₀ y₀
      let one := butterfly x₁ y₁
      (.branch zero.1 one.1, .branch zero.2 one.2)

private def WalshCertificateTree.allNatAbsLe (bound : ℕ) :
    {n : ℕ} → WalshCertificateTree n → Bool
  | 0, .leaf value => decide (value.natAbs ≤ bound)
  | _ + 1, .branch zero one =>
      zero.allNatAbsLe bound && one.allNatAbsLe bound

private def WalshCertificateTree.allFrequencies :
    {n : ℕ} → WalshCertificateTree n →
      (FABL.F₂Cube n → ℤ → Bool) → Bool
  | 0, .leaf value, predicate => predicate 0 value
  | _ + 1, .branch zero one, predicate =>
      zero.allFrequencies (fun a value ↦ predicate (Fin.cons 0 a) value) &&
        one.allFrequencies (fun a value ↦ predicate (Fin.cons 1 a) value)

private theorem WalshCertificateTree.allFrequencies_sound
    {n : ℕ} (tree : WalshCertificateTree n)
    (predicate : FABL.F₂Cube n → ℤ → Bool)
    (h : tree.allFrequencies predicate = true)
    (a : FABL.F₂Cube n) : predicate a (tree.eval a) = true := by
  induction n with
  | zero =>
      cases tree with
      | leaf value =>
          have ha : a = 0 := Subsingleton.elim _ _
          subst a
          exact h
  | succ n ih =>
      cases tree with
      | branch zero one =>
          have hparts := Bool.and_eq_true_iff.mp h
          by_cases ha : a 0 = 0
          · rw [WalshCertificateTree.eval, if_pos ha]
            have hzero := ih zero
              (fun tail value ↦ predicate (Fin.cons 0 tail) value)
              hparts.1 (Fin.tail a)
            have hcons := Fin.cons_self_tail a
            rw [ha] at hcons
            simpa only [hcons] using hzero
          · rw [WalshCertificateTree.eval, if_neg ha]
            have ha_one : a 0 = 1 := Fin.eq_one_of_ne_zero _ ha
            have hone := ih one
              (fun tail value ↦ predicate (Fin.cons 1 tail) value)
              hparts.2 (Fin.tail a)
            have hcons := Fin.cons_self_tail a
            rw [ha_one] at hcons
            simpa only [hcons] using hone

private theorem WalshCertificateTree.eval_butterfly
    {n : ℕ} (x y : WalshCertificateTree n) (a : FABL.F₂Cube n) :
    ((x.butterfly y).1.eval a, (x.butterfly y).2.eval a) =
      (x.eval a + y.eval a, x.eval a - y.eval a) := by
  induction n with
  | zero =>
      cases x with
      | leaf x =>
          cases y with
          | leaf y => simp [butterfly, eval]
  | succ n ih =>
      cases x with
      | branch x₀ x₁ =>
          cases y with
          | branch y₀ y₁ =>
              by_cases ha : a 0 = 0
              · simpa [butterfly, eval, ha] using
                  ih x₀ y₀ (Fin.tail a)
              · simpa [butterfly, eval, ha] using
                  ih x₁ y₁ (Fin.tail a)

private theorem WalshCertificateTree.natAbs_eval_le_of_allNatAbsLe
    {n bound : ℕ} (tree : WalshCertificateTree n)
    (h : tree.allNatAbsLe bound = true) (a : FABL.F₂Cube n) :
    (tree.eval a).natAbs ≤ bound := by
  induction n with
  | zero =>
      cases tree with
      | leaf value =>
          change decide (value.natAbs ≤ bound) = true at h
          simpa [eval] using of_decide_eq_true h
  | succ n ih =>
      cases tree with
      | branch zero one =>
          have hparts := Bool.and_eq_true_iff.mp h
          by_cases ha : a 0 = 0
          · simpa [eval, ha] using ih zero hparts.1 (Fin.tail a)
          · simpa [eval, ha] using ih one hparts.2 (Fin.tail a)

private def fastWalshCertificateTree :
    (n : ℕ) → BooleanFunction n → WalshCertificateTree n
  | 0, f => .leaf (bitSignInt (f 0))
  | n + 1, f =>
      let lower := fastWalshCertificateTree n (fun x ↦ f (Fin.cons 0 x))
      let upper := fastWalshCertificateTree n (fun x ↦ f (Fin.cons 1 x))
      let transformed := lower.butterfly upper
      .branch transformed.1 transformed.2

private theorem walshTransform_succ
    (f : BooleanFunction (n + 1)) (a : FABL.F₂Cube (n + 1)) :
    walshTransform f a =
      if a 0 = 0 then
        walshTransform (fun x ↦ f (Fin.cons 0 x)) (Fin.tail a) +
          walshTransform (fun x ↦ f (Fin.cons 1 x)) (Fin.tail a)
      else
        walshTransform (fun x ↦ f (Fin.cons 0 x)) (Fin.tail a) -
          walshTransform (fun x ↦ f (Fin.cons 1 x)) (Fin.tail a) := by
  classical
  unfold walshTransform
  rw [← Equiv.sum_comp (Fin.consEquiv
    (fun _ : Fin (n + 1) ↦ FABL.𝔽₂))]
  rw [Fintype.sum_prod_type]
  change (∑ b : FABL.𝔽₂, ∑ x : FABL.F₂Cube n,
      walshTerm f a (Fin.cons b x)) = _
  rw [show (Finset.univ : Finset FABL.𝔽₂) = {0, 1} by rfl]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton]
  by_cases ha : a 0 = 0
  · rw [if_pos ha]
    congr 1
    · apply Finset.sum_congr rfl
      intro x _hx
      simp [walshTerm, FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ,
        ha, Fin.tail]
    · apply Finset.sum_congr rfl
      intro x _hx
      simp [walshTerm, FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ,
        ha, Fin.tail]
  · rw [if_neg ha]
    have ha_one : a 0 = 1 := Fin.eq_one_of_ne_zero _ ha
    congr 1
    · apply Finset.sum_congr rfl
      intro x _hx
      simp [walshTerm, FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ,
        ha_one, Fin.tail]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [show walshTerm f a (Fin.cons 1 x) =
          bitSignInt
            ((f (Fin.cons 1 x) + FABL.f₂DotProduct (Fin.tail a) x) + 1) by
        simp [walshTerm, FABL.f₂DotProduct, dotProduct,
          Fin.sum_univ_succ, ha_one, Fin.tail]
        ring_nf]
      rw [show bitSignInt
          ((f (Fin.cons 1 x) + FABL.f₂DotProduct (Fin.tail a) x) + 1) =
          bitSignInt
              (f (Fin.cons 1 x) + FABL.f₂DotProduct (Fin.tail a) x) *
            bitSignInt 1 by
        exact show bitSignInt (_ + _) = _ from by
          unfold bitSignInt
          rw [FABL.signEncode_add]
          rfl]
      simp [walshTerm, bitSignInt]

private theorem fastWalshCertificateTree_correct
    (n : ℕ) (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (fastWalshCertificateTree n f).eval a = walshTransform f a := by
  induction n with
  | zero =>
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      rw [fastWalshCertificateTree, WalshCertificateTree.eval,
        walshTransform, Fintype.sum_unique]
      unfold walshTerm
      have hdot (x y : FABL.F₂Cube 0) : FABL.f₂DotProduct x y = 0 := by
        simp [FABL.f₂DotProduct, dotProduct]
      rw [hdot]
      rw [add_zero]
      exact congrArg (fun x ↦ bitSignInt (f x)) (Subsingleton.elim _ _)
  | succ n ih =>
      rw [walshTransform_succ]
      simp only [fastWalshCertificateTree, WalshCertificateTree.eval]
      let lower := fastWalshCertificateTree n
        (fun x ↦ f (Fin.cons 0 x))
      let upper := fastWalshCertificateTree n
        (fun x ↦ f (Fin.cons 1 x))
      have hbutterfly := lower.eval_butterfly upper (Fin.tail a)
      by_cases ha : a 0 = 0
      · rw [if_pos ha, if_pos ha]
        have hzero := congrArg Prod.fst hbutterfly
        simpa [lower, upper, ih] using hzero
      · rw [if_neg ha, if_neg ha]
        have hone := congrArg Prod.snd hbutterfly
        simpa [lower, upper, ih] using hone

private theorem kavutYucelFunction9_reflection_certificate :
    (fastWalshCertificateTree 9 kavutYucelFunction9).allNatAbsLe 28 = true := by
  decide

/-- Kernel-checked exhaustive certificate for the Walsh upper bound of the
Kavut--Yücel truth table. -/
theorem kavutYucelFunction9_walsh_bound
    (a : FABL.F₂Cube 9) :
    (walshTransform kavutYucelFunction9 a).natAbs ≤ 28 := by
  rw [← fastWalshCertificateTree_correct]
  exact WalshCertificateTree.natAbs_eval_le_of_allNatAbsLe
    (fastWalshCertificateTree 9 kavutYucelFunction9)
    kavutYucelFunction9_reflection_certificate a

private theorem kavutYucelFunction9_witness_certificate :
    (fastWalshCertificateTree 9 kavutYucelFunction9).eval
      (f₂CubeOfNat 9 7) = 28 := by
  decide

/-- Frequency seven witnesses that the certified Walsh upper bound is sharp. -/
theorem kavutYucelFunction9_walsh_witness :
    walshTransform kavutYucelFunction9 (f₂CubeOfNat 9 7) = 28 := by
  rw [← fastWalshCertificateTree_correct]
  exact kavutYucelFunction9_witness_certificate

/-- The Kavut--Yücel function has maximum Walsh magnitude exactly 28. -/
theorem maxWalshMagnitude_kavutYucelFunction9 :
    maxWalshMagnitude kavutYucelFunction9 = 28 := by
  apply Nat.le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty
      (fun a : FABL.F₂Cube 9 ↦
        (walshTransform kavutYucelFunction9 a).natAbs)
      fun a _ha ↦ kavutYucelFunction9_walsh_bound a
  · have hw := Finset.le_sup'
      (fun a : FABL.F₂Cube 9 ↦ (walshTransform kavutYucelFunction9 a).natAbs)
      (Finset.mem_univ (f₂CubeOfNat 9 7))
    simpa [maxWalshMagnitude, kavutYucelFunction9_walsh_witness] using hw

/-- The Kavut--Yücel truth table has nonlinearity 242. -/
theorem nonlinearity_kavutYucelFunction9 :
    nonlinearity kavutYucelFunction9 = 242 := by
  have h := two_mul_nonlinearity_add_maxWalshMagnitude kavutYucelFunction9
  rw [maxWalshMagnitude_kavutYucelFunction9] at h
  omega

/-- The Boolean direct sum on two disjoint coordinate blocks. -/
def booleanDirectSum {k l : ℕ}
    (f : BooleanFunction k) (g : BooleanFunction l) :
    BooleanFunction (k + l) :=
  fun z ↦
    let p := (Fin.appendEquiv k l).symm z
    f p.1 + g p.2

/-- The sign view of a Boolean direct sum is FABL's direct product. -/
theorem realSignView_booleanDirectSum
    {k l : ℕ} (f : BooleanFunction k) (g : BooleanFunction l) :
    realSignView (booleanDirectSum f g) =
      FABL.bentDirectProduct (realSignView f) (realSignView g) := by
  funext z
  unfold booleanDirectSum FABL.bentDirectProduct
    realSignView FABL.realSignEncodedFunction FABL.signEncodedFunction
  rw [FABL.signEncode_add]
  simp [FABL.signValue]

/-- Raw Walsh transforms multiply under Boolean direct sums. -/
theorem walshTransform_booleanDirectSum_append
    {k l : ℕ} (f : BooleanFunction k) (g : BooleanFunction l)
    (a : FABL.F₂Cube k) (b : FABL.F₂Cube l) :
    walshTransform (booleanDirectSum f g) (Fin.append a b) =
      walshTransform f a * walshTransform g b := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    realSignView_booleanDirectSum,
    FABL.vectorFourierCoeff_bentDirectProduct_append]
  rw [pow_add]
  ring

/-- Extend a Boolean function by a complete even-dimensional inner-product bent block. -/
def completeBentExtension {k : ℕ} (f : BooleanFunction k) (m : ℕ) :
    BooleanFunction (k + (m + m)) :=
  booleanDirectSum f FABL.innerProductModTwoBit

/-- The sign view of a complete bent extension is FABL's direct product. -/
theorem realSignView_completeBentExtension
    {k : ℕ} (f : BooleanFunction k) (m : ℕ) :
    realSignView (completeBentExtension f m) =
      FABL.bentDirectProduct (realSignView f)
        (FABL.innerProductModTwo m) := by
  rw [← show realSignView FABL.innerProductModTwoBit =
      FABL.innerProductModTwo m by rfl]
  exact realSignView_booleanDirectSum f FABL.innerProductModTwoBit

/-- The raw Walsh transform of a complete bent extension factors over the two blocks. -/
theorem walshTransform_completeBentExtension_append
    {k : ℕ} (f : BooleanFunction k) (m : ℕ)
    (a : FABL.F₂Cube k) (b : FABL.F₂Cube (m + m)) :
    (walshTransform (completeBentExtension f m) (Fin.append a b) : ℝ) =
      (walshTransform f a : ℝ) *
        (walshTransform FABL.innerProductModTwoBit b : ℝ) := by
  exact_mod_cast walshTransform_booleanDirectSum_append
    f FABL.innerProductModTwoBit a b

/-- The Kavut--Yücel function extended by a complete `2m`-variable bent block. -/
def kavutYucelBentExtension (m : ℕ) :
    BooleanFunction (9 + (m + m)) :=
  completeBentExtension kavutYucelFunction9 m

/-- The sign view of the Kavut--Yücel extension is FABL's direct product. -/
theorem realSignView_kavutYucelBentExtension (m : ℕ) :
    realSignView (kavutYucelBentExtension m) =
      FABL.bentDirectProduct (realSignView kavutYucelFunction9)
        (FABL.innerProductModTwo m) := by
  simpa [kavutYucelBentExtension] using
    realSignView_completeBentExtension kavutYucelFunction9 m

/-- The raw Walsh transform of the Kavut--Yücel extension factors over the two blocks. -/
theorem walshTransform_kavutYucelBentExtension_append
    (m : ℕ) (a : FABL.F₂Cube 9) (b : FABL.F₂Cube (m + m)) :
    (walshTransform (kavutYucelBentExtension m) (Fin.append a b) : ℝ) =
      (walshTransform kavutYucelFunction9 a : ℝ) *
        (walshTransform FABL.innerProductModTwoBit b : ℝ) := by
  simpa [kavutYucelBentExtension] using
    walshTransform_completeBentExtension_append
      kavutYucelFunction9 m a b

/-- The complete `2m`-variable inner-product block has raw Walsh magnitude `2^m`. -/
theorem natAbs_walshTransform_innerProductModTwoBit
    (m : ℕ) (b : FABL.F₂Cube (m + m)) :
    (walshTransform FABL.innerProductModTwoBit b).natAbs = 2 ^ m := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_natAbs, Int.cast_abs,
    walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  rw [show realSignView FABL.innerProductModTwoBit =
      FABL.innerProductModTwo m by rfl]
  rw [abs_mul, abs_of_nonneg (by positivity),
    FABL.abs_vectorFourierCoeff_innerProductModTwo]
  rw [pow_add]
  field_simp
  norm_cast

/-- Raw Walsh magnitudes of a complete bent extension are the seed magnitudes
scaled by `2^m`. -/
theorem natAbs_walshTransform_completeBentExtension_append
    {k : ℕ} (f : BooleanFunction k) (m : ℕ)
    (a : FABL.F₂Cube k) (b : FABL.F₂Cube (m + m)) :
    (walshTransform (completeBentExtension f m) (Fin.append a b)).natAbs =
      (walshTransform f a).natAbs * 2 ^ m := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  rw [walshTransform_completeBentExtension_append]
  rw [abs_mul]
  congr 1
  have hipCast := congrArg (fun q : ℕ ↦ (q : ℝ))
    (natAbs_walshTransform_innerProductModTwoBit m b)
  rw [Nat.cast_natAbs, Int.cast_abs] at hipCast
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hipCast

/-- A complete bent extension scales the seed's maximum raw Walsh magnitude
by `2^m`. -/
theorem maxWalshMagnitude_completeBentExtension
    {k : ℕ} (f : BooleanFunction k) (m : ℕ) :
    maxWalshMagnitude (completeBentExtension f m) =
      maxWalshMagnitude f * 2 ^ m := by
  unfold maxWalshMagnitude
  apply Nat.le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
      (fun γ : FABL.F₂Cube (k + (m + m)) ↦
        (walshTransform (completeBentExtension f m) γ).natAbs)
    intro γ _hγ
    let p := (Fin.appendEquiv k (m + m)).symm γ
    have hγ : Fin.append p.1 p.2 = γ :=
      (Fin.appendEquiv k (m + m)).apply_symm_apply γ
    rw [← hγ, natAbs_walshTransform_completeBentExtension_append]
    exact Nat.mul_le_mul_right (2 ^ m)
      (Finset.le_sup'
        (fun a : FABL.F₂Cube k ↦ (walshTransform f a).natAbs)
        (Finset.mem_univ p.1))
  · obtain ⟨a, _ha, ha⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube k)))
      Finset.univ_nonempty
      (fun a : FABL.F₂Cube k ↦ (walshTransform f a).natAbs)
    have hw := Finset.le_sup'
      (fun γ : FABL.F₂Cube (k + (m + m)) ↦
        (walshTransform (completeBentExtension f m) γ).natAbs)
      (Finset.mem_univ
        (Fin.append a (0 : FABL.F₂Cube (m + m))))
    rw [natAbs_walshTransform_completeBentExtension_append, ← ha] at hw
    exact hw

/-- Complete bent extension preserves balancedness of the seed. -/
theorem isBalanced_completeBentExtension
    {k : ℕ} (f : BooleanFunction k) (m : ℕ) (hf : IsBalanced f) :
    IsBalanced (completeBentExtension f m) := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero] at hf ⊢
  have hzero :
      Fin.append (0 : FABL.F₂Cube k) (0 : FABL.F₂Cube (m + m)) =
        (0 : FABL.F₂Cube (k + (m + m))) := by
    funext i
    refine Fin.addCases (fun l ↦ ?_) (fun r ↦ ?_) i <;> simp
  have hreal :
      (walshTransform (completeBentExtension f m) 0 : ℝ) = 0 := by
    calc
      (walshTransform (completeBentExtension f m) 0 : ℝ) =
          (walshTransform (completeBentExtension f m)
            (Fin.append (0 : FABL.F₂Cube k)
              (0 : FABL.F₂Cube (m + m))) : ℝ) := by rw [hzero]
      _ =
          (walshTransform f 0 : ℝ) *
            (walshTransform FABL.innerProductModTwoBit
              (0 : FABL.F₂Cube (m + m)) : ℝ) := by
        exact walshTransform_completeBentExtension_append
          f m (0 : FABL.F₂Cube k) (0 : FABL.F₂Cube (m + m))
      _ = 0 := by rw [hf]; norm_num
  exact_mod_cast hreal

/-- The quadratic odd-dimensional construction: a complete inner-product
block together with one dummy coordinate. -/
def oddQuadraticFunction (m : ℕ) : BooleanFunction ((m + m) + 1) :=
  fun z ↦ FABL.innerProductModTwoBit (Fin.tail z)

/-- The dummy coordinate doubles the inner-product Walsh transform at zero
frequency and annihilates it at frequency one. -/
theorem walshTransform_oddQuadraticFunction
    (m : ℕ) (a : FABL.F₂Cube ((m + m) + 1)) :
    walshTransform (oddQuadraticFunction m) a =
      if a 0 = 0 then
        2 * walshTransform FABL.innerProductModTwoBit (Fin.tail a)
      else 0 := by
  rw [walshTransform_succ]
  by_cases ha : a 0 = 0
  · simp [ha, oddQuadraticFunction, two_mul]
  · simp [ha, oddQuadraticFunction]

/-- The quadratic odd-dimensional construction has maximum raw Walsh
magnitude `2^(m+1)`. -/
theorem maxWalshMagnitude_oddQuadraticFunction (m : ℕ) :
    maxWalshMagnitude (oddQuadraticFunction m) = 2 ^ (m + 1) := by
  unfold maxWalshMagnitude
  apply Nat.le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
      (fun a : FABL.F₂Cube ((m + m) + 1) ↦
        (walshTransform (oddQuadraticFunction m) a).natAbs)
    intro a _ha
    rw [walshTransform_oddQuadraticFunction]
    by_cases ha : a 0 = 0
    · rw [if_pos ha, Int.natAbs_mul,
        natAbs_walshTransform_innerProductModTwoBit]
      simp [pow_succ, Nat.mul_comm]
    · simp [ha]
  · have hw := Finset.le_sup'
      (fun a : FABL.F₂Cube ((m + m) + 1) ↦
        (walshTransform (oddQuadraticFunction m) a).natAbs)
      (Finset.mem_univ (0 : FABL.F₂Cube ((m + m) + 1)))
    rw [walshTransform_oddQuadraticFunction, if_pos (by simp),
      Int.natAbs_mul, natAbs_walshTransform_innerProductModTwoBit] at hw
    simpa [pow_succ, Nat.mul_comm] using hw

/-- The quadratic odd-dimensional construction attains the quadratic
nonlinearity bound. -/
theorem nonlinearity_oddQuadraticFunction (m : ℕ) :
    nonlinearity (oddQuadraticFunction m) = 2 ^ (m + m) - 2 ^ m := by
  have h := two_mul_nonlinearity_add_maxWalshMagnitude
    (oddQuadraticFunction m)
  rw [maxWalshMagnitude_oddQuadraticFunction] at h
  have hdim : 2 ^ ((m + m) + 1) = 2 * 2 ^ (m + m) := by
    rw [pow_succ]
    ring
  have hmag : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  rw [hdim, hmag] at h
  omega

/-- In every odd dimension, the maximum nonlinearity is at least the
quadratic bound. -/
theorem quadraticBound_le_maximumNonlinearity_of_odd
    (hn : Odd n) :
    2 ^ (n - 1) - 2 ^ ((n - 1) / 2) ≤ maximumNonlinearity n := by
  obtain ⟨m, hm⟩ := hn
  have hnform : n = (m + m) + 1 := by omega
  rw [hnform]
  have hsub : (m + m) + 1 - 1 = m + m := by omega
  have hhalf : (m + m) / 2 = m := by omega
  simpa only [hsub, hhalf, nonlinearity_oddQuadraticFunction] using
    nonlinearity_le_maximumNonlinearity (oddQuadraticFunction m)

/-- The maximum nonlinearity satisfies Carlet's covering-radius bound in
every dimension. -/
theorem maximumNonlinearity_cast_le_relation_36 (n : ℕ) :
    (maximumNonlinearity n : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
  obtain ⟨f, hf⟩ := exists_nonlinearity_eq_maximumNonlinearity n
  rw [← hf]
  exact nonlinearity_cast_le_relation_36 f

/-- Carlet's lower quadratic bound and upper covering-radius bound for the
best nonlinearity in odd dimension. -/
theorem maximumNonlinearity_odd_bounds
    (hn : Odd n) :
    2 ^ (n - 1) - 2 ^ ((n - 1) / 2) ≤ maximumNonlinearity n ∧
      (maximumNonlinearity n : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) - 1) -
          (2 : ℝ) ^ ((n : ℝ) / 2 - 1) :=
  ⟨quadraticBound_le_maximumNonlinearity_of_odd hn,
    maximumNonlinearity_cast_le_relation_36 n⟩

/-- The best one-variable nonlinearity is the quadratic-bound value zero. -/
theorem maximumNonlinearity_one : maximumNonlinearity 1 = 0 := by
  obtain ⟨f, hf⟩ := exists_nonlinearity_eq_maximumNonlinearity 1
  have hupper := nonlinearity_cast_le_coveringRadius f
  rw [hf] at hupper
  have hpow : (2 : ℝ) ^ (1 : ℕ) = 2 := by norm_num
  rw [hpow] at hupper
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlt : (maximumNonlinearity 1 : ℝ) < 1 := by
    linarith
  have hnat : maximumNonlinearity 1 < 1 := by
    exact_mod_cast hlt
  omega

/-- The best three-variable nonlinearity is the quadratic-bound value two. -/
theorem maximumNonlinearity_three : maximumNonlinearity 3 = 2 := by
  have hlower := quadraticBound_le_maximumNonlinearity_of_odd
    (n := 3) (by decide)
  obtain ⟨f, hf⟩ := exists_nonlinearity_eq_maximumNonlinearity 3
  have hupper := nonlinearity_cast_le_coveringRadius f
  rw [hf] at hupper
  have hpow : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num
  rw [hpow] at hupper
  have hsqrt : 2 < Real.sqrt 8 := by
    calc
      (2 : ℝ) = Real.sqrt 4 := by norm_num
      _ < Real.sqrt 8 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlt : (maximumNonlinearity 3 : ℝ) < 3 := by
    linarith
  have hnat : maximumNonlinearity 3 < 3 := by
    exact_mod_cast hlt
  norm_num at hlower
  omega

/-- Raw Walsh magnitudes of the extension are the base magnitudes scaled by `2^m`. -/
theorem natAbs_walshTransform_kavutYucelBentExtension_append
    (m : ℕ) (a : FABL.F₂Cube 9) (b : FABL.F₂Cube (m + m)) :
    (walshTransform (kavutYucelBentExtension m)
        (Fin.append a b)).natAbs =
      (walshTransform kavutYucelFunction9 a).natAbs * 2 ^ m := by
  simpa [kavutYucelBentExtension] using
    natAbs_walshTransform_completeBentExtension_append
      kavutYucelFunction9 m a b

/-- The extended function has maximum raw Walsh magnitude `28 * 2^m`. -/
theorem maxWalshMagnitude_kavutYucelBentExtension (m : ℕ) :
    maxWalshMagnitude (kavutYucelBentExtension m) = 28 * 2 ^ m := by
  rw [kavutYucelBentExtension,
    maxWalshMagnitude_completeBentExtension,
    maxWalshMagnitude_kavutYucelFunction9]

/-- The exact nonlinearity of the direct-product extension. -/
theorem nonlinearity_kavutYucelBentExtension (m : ℕ) :
    nonlinearity (kavutYucelBentExtension m) =
      2 ^ (8 + (m + m)) - 14 * 2 ^ m := by
  have h := two_mul_nonlinearity_add_maxWalshMagnitude
    (kavutYucelBentExtension m)
  rw [maxWalshMagnitude_kavutYucelBentExtension] at h
  have hpow : 2 ^ (9 + (m + m)) = 2 * 2 ^ (8 + (m + m)) := by
    rw [show 9 + (m + m) = (8 + (m + m)) + 1 by omega, pow_succ]
    ring
  rw [hpow] at h
  omega

/-- Every member of the direct-product family strictly exceeds the odd-dimensional
quadratic nonlinearity bound. -/
theorem quadraticBound_lt_nonlinearity_kavutYucelBentExtension (m : ℕ) :
    2 ^ (8 + (m + m)) - 2 ^ (4 + m) <
      nonlinearity (kavutYucelBentExtension m) := by
  rw [nonlinearity_kavutYucelBentExtension]
  have hsmall : 14 * 2 ^ m < 16 * 2 ^ m := by
    have hpositive : 0 < 2 ^ m := Nat.pow_pos (by omega)
    omega
  have hfour : 2 ^ (4 + m) = 16 * 2 ^ m := by
    rw [pow_add]
    norm_num
  have hlarge : 16 * 2 ^ m ≤ 2 ^ (8 + (m + m)) := by
    rw [← hfour]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  rw [hfour]
  exact Nat.sub_lt_sub_left (hsmall.trans_le hlarge) hsmall

/-- In every odd dimension above seven, some Boolean function strictly exceeds
the quadratic nonlinearity bound. -/
theorem exists_nonlinearity_gt_quadraticBound_of_odd
    (hn : Odd n) (hn7 : 7 < n) :
    ∃ f : BooleanFunction n,
      2 ^ (n - 1) - 2 ^ ((n - 1) / 2) < nonlinearity f := by
  obtain ⟨k, hk⟩ := hn
  have hk4 : 4 ≤ k := by omega
  let m := k - 4
  have hnform : n = 9 + (m + m) := by
    dsimp [m]
    omega
  rw [hnform]
  refine ⟨kavutYucelBentExtension m, ?_⟩
  have hsub : 9 + (m + m) - 1 = 8 + (m + m) := by omega
  have hhalf : (8 + (m + m)) / 2 = 4 + m := by omega
  simpa only [hsub, hhalf] using
    quadraticBound_lt_nonlinearity_kavutYucelBentExtension m

/-- In every odd dimension above seven, the maximum nonlinearity strictly
exceeds the quadratic bound. -/
theorem quadraticBound_lt_maximumNonlinearity_of_odd
    (hn : Odd n) (hn7 : 7 < n) :
    2 ^ (n - 1) - 2 ^ ((n - 1) / 2) < maximumNonlinearity n := by
  obtain ⟨f, hf⟩ := exists_nonlinearity_gt_quadraticBound_of_odd hn hn7
  exact hf.trans_le (nonlinearity_le_maximumNonlinearity f)

/-! ### Balanced Maitra--Kavut--Yücel family -/

/-- Toggle a finite set of truth-table positions. -/
def flipOn {k : ℕ}
    (f : BooleanFunction k) (points : Finset (FABL.F₂Cube k)) :
    BooleanFunction k :=
  fun x ↦ f x + if x ∈ points then 1 else 0

namespace MaitraKavutYucel

/-- BFCA 2008, p. 114: the nine-variable seed truth table. -/
def seedTruthTable : ℕ :=
  0x125425D30A398F36508C06817BEE122E250D973314F976AED58A3EA9120DA4FE * 2 ^ 256 +
    0x0E4D4575C42DD0426365EBA7FC5F45BE9B2F336981B5E1863618F49474F6FE00

/-- The nine-variable seed, with source bits read left-to-right. -/
def seedFunction9 : BooleanFunction 9 :=
  fun x ↦
    if seedTruthTable.testBit (511 - f₂CubeNatIndex x) then 1 else 0

/-- The paper's linear shift `w₁ = (0,0,0,0,1,1,0,1,1)`. -/
def shiftFrequency9 : FABL.F₂Cube 9 :=
  f₂CubeOfNat 9 27

/-- The shifted seed `f₁(x) = f(x) ⊕ ⟨w₁,x⟩`. -/
def shiftedSeedFunction9 : BooleanFunction 9 :=
  fun x ↦
    seedFunction9 x + FABL.f₂DotProduct shiftFrequency9 x

/-- BFCA 2008, p. 115: the four-variable bent truth table. -/
def bentTruthTable : ℕ :=
  0x0356

/-- The four-variable bent component, with source bits read left-to-right. -/
def bentFunction4 : BooleanFunction 4 :=
  fun y ↦
    if bentTruthTable.testBit (15 - f₂CubeNatIndex y) then 1 else 0

/-- The initial thirteen-variable direct sum, of nonlinearity `4040`. -/
def initialFunction13 : BooleanFunction (9 + 4) :=
  booleanDirectSum shiftedSeedFunction9 bentFunction4

/-- BFCA 2008, p. 114: the eight toggled truth-table positions. -/
def flipPointList13 :
    List (FABL.F₂Cube (9 + 4)) :=
  [ f₂CubeOfNat 13 4667,
    f₂CubeOfNat 13 4758,
    f₂CubeOfNat 13 4807,
    f₂CubeOfNat 13 4823,
    f₂CubeOfNat 13 4913,
    f₂CubeOfNat 13 5042,
    f₂CubeOfNat 13 8133,
    f₂CubeOfNat 13 8187 ]

/-- The finite set of the eight published toggle positions. -/
def flipPoints13 :
    Finset (FABL.F₂Cube (9 + 4)) :=
  flipPointList13.toFinset

end MaitraKavutYucel

/-- Maitra--Kavut--Yücel's balanced thirteen-variable function from BFCA 2008:
the direct sum printed in Section 3, with the eight published positions toggled. -/
def maitraKavutYucelFunction13 : BooleanFunction 13 :=
  flipOn MaitraKavutYucel.initialFunction13 MaitraKavutYucel.flipPoints13

private def walshCharacterInt {k : ℕ}
    (a x : FABL.F₂Cube k) : ℤ :=
  bitSignInt (FABL.f₂DotProduct a x)

private def maitraKavutYucelPointsSix9 : List (FABL.F₂Cube 9) :=
  [59, 150, 199, 215, 305, 434].map (f₂CubeOfNat 9)

private def maitraKavutYucelPointsTwo9 : List (FABL.F₂Cube 9) :=
  [453, 507].map (f₂CubeOfNat 9)

private def walshCharacterSum
    {k : ℕ} (a : FABL.F₂Cube k) (points : List (FABL.F₂Cube k)) : ℤ :=
  (points.map (walshCharacterInt a)).sum

private def maitraKavutYucelSeedSpectrumCondition
    (a : FABL.F₂Cube 9) (value : ℤ) : Bool :=
  decide (value.natAbs ≤ 20 ∨
    (value.natAbs = 28 ∧
      (walshCharacterSum a maitraKavutYucelPointsSix9 +
          walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs ≤ 4 ∧
      (walshCharacterSum a maitraKavutYucelPointsSix9 -
          walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs ≤ 4))

private theorem maitraKavutYucelSeedSpectrum_certificate :
    (fastWalshCertificateTree 9
      MaitraKavutYucel.shiftedSeedFunction9).allFrequencies
        maitraKavutYucelSeedSpectrumCondition = true := by
  decide

private theorem maitraKavutYucelSeedSpectrum
    (a : FABL.F₂Cube 9) :
    (walshTransform MaitraKavutYucel.shiftedSeedFunction9 a).natAbs ≤ 20 ∨
      ((walshTransform MaitraKavutYucel.shiftedSeedFunction9 a).natAbs = 28 ∧
        (walshCharacterSum a maitraKavutYucelPointsSix9 +
            walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs ≤ 4 ∧
        (walshCharacterSum a maitraKavutYucelPointsSix9 -
            walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs ≤ 4) := by
  have h := WalshCertificateTree.allFrequencies_sound
    (fastWalshCertificateTree 9 MaitraKavutYucel.shiftedSeedFunction9)
    maitraKavutYucelSeedSpectrumCondition
    maitraKavutYucelSeedSpectrum_certificate a
  rw [fastWalshCertificateTree_correct] at h
  exact of_decide_eq_true h

private theorem maitraKavutYucelBentSpectrum_certificate :
    (fastWalshCertificateTree 4
      MaitraKavutYucel.bentFunction4).allFrequencies
        (fun _ value ↦ decide (value.natAbs = 4)) = true := by
  decide

private theorem maitraKavutYucelBentSpectrum (b : FABL.F₂Cube 4) :
    (walshTransform MaitraKavutYucel.bentFunction4 b).natAbs = 4 := by
  have h := WalshCertificateTree.allFrequencies_sound
    (fastWalshCertificateTree 4 MaitraKavutYucel.bentFunction4)
    (fun _ value ↦ decide (value.natAbs = 4))
    maitraKavutYucelBentSpectrum_certificate b
  rw [fastWalshCertificateTree_correct] at h
  exact of_decide_eq_true h

private theorem maitraKavutYucelBitSignInt_add_one (b : FABL.𝔽₂) :
    bitSignInt (b + 1) = -bitSignInt b := by
  fin_cases b <;> rfl

private theorem maitraKavutYucelWalshTerm_flipOn
    {n : ℕ} (f : BooleanFunction n) (points : Finset (FABL.F₂Cube n))
    (a x : FABL.F₂Cube n) :
    walshTerm (flipOn f points) a x =
      if x ∈ points then -walshTerm f a x else walshTerm f a x := by
  by_cases hx : x ∈ points
  · rw [if_pos hx]
    unfold walshTerm flipOn
    rw [if_pos hx]
    rw [show f x + 1 + FABL.f₂DotProduct a x =
        (f x + FABL.f₂DotProduct a x) + 1 by abel]
    exact maitraKavutYucelBitSignInt_add_one _
  · rw [if_neg hx]
    simp [walshTerm, flipOn, hx]

private theorem maitraKavutYucelWalshTransform_flipOn
    {n : ℕ} (f : BooleanFunction n) (points : Finset (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) :
    walshTransform (flipOn f points) a =
      walshTransform f a - 2 * ∑ x ∈ points, walshTerm f a x := by
  classical
  unfold walshTransform
  rw [show (∑ x, walshTerm (flipOn f points) a x) =
      ∑ x, if x ∈ points then -walshTerm f a x else walshTerm f a x by
    apply Finset.sum_congr rfl
    intro x _hx
    exact maitraKavutYucelWalshTerm_flipOn f points a x]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, Finset.sum_neg_distrib]
  have hsplit := Finset.sum_sdiff
    (f := fun x ↦ walshTerm f a x)
    (show points ⊆ (Finset.univ : Finset (FABL.F₂Cube n)) by simp)
  calc
    -∑ x ∈ points, walshTerm f a x +
          ∑ x ∈ (Finset.univ : Finset (FABL.F₂Cube n)) \ points,
            walshTerm f a x =
        ((∑ x ∈ (Finset.univ : Finset (FABL.F₂Cube n)) \ points,
              walshTerm f a x) +
            ∑ x ∈ points, walshTerm f a x) -
          2 * ∑ x ∈ points, walshTerm f a x := by ring
    _ = (∑ x : FABL.F₂Cube n, walshTerm f a x) -
          2 * ∑ x ∈ points, walshTerm f a x := by rw [hsplit]

private theorem walshCharacterInt_append
    {n m : ℕ} (a x : FABL.F₂Cube n) (b y : FABL.F₂Cube m) :
    walshCharacterInt (Fin.append a b) (Fin.append x y) =
      walshCharacterInt a x * walshCharacterInt b y := by
  unfold walshCharacterInt bitSignInt
  rw [FABL.f₂DotProduct_append, FABL.signEncode_add]
  rfl

private theorem maitraKavutYucelInitialFunction13_zero_on_flipPoints
    (p : FABL.F₂Cube (9 + 4)) (hp : p ∈ MaitraKavutYucel.flipPoints13) :
    MaitraKavutYucel.initialFunction13 p = 0 := by
  have hp' :
      p = f₂CubeOfNat 13 4667 ∨
      p = f₂CubeOfNat 13 4758 ∨
      p = f₂CubeOfNat 13 4807 ∨
      p = f₂CubeOfNat 13 4823 ∨
      p = f₂CubeOfNat 13 4913 ∨
      p = f₂CubeOfNat 13 5042 ∨
      p = f₂CubeOfNat 13 8133 ∨
      p = f₂CubeOfNat 13 8187 := by
    simpa only [MaitraKavutYucel.flipPoints13, List.mem_toFinset,
      MaitraKavutYucel.flipPointList13, List.mem_cons, List.mem_nil_iff,
      or_false] using hp
  rcases hp' with h | h | h | h | h | h | h | h <;> subst p <;> decide

private theorem maitraKavutYucelFlipWalshTerm_eq_character
    (a p : FABL.F₂Cube (9 + 4)) (hp : p ∈ MaitraKavutYucel.flipPoints13) :
    walshTerm MaitraKavutYucel.initialFunction13 a p = walshCharacterInt a p := by
  rw [walshTerm, maitraKavutYucelInitialFunction13_zero_on_flipPoints p hp, zero_add]
  rfl

private theorem maitraKavutYucelFlipCharacterSum
    (a : FABL.F₂Cube 9) (b : FABL.F₂Cube 4) :
    (∑ p ∈ MaitraKavutYucel.flipPoints13,
        walshCharacterInt (Fin.append a b) p) =
      walshCharacterInt b (f₂CubeOfNat 4 9) *
          walshCharacterSum a maitraKavutYucelPointsSix9 +
        walshCharacterInt b (f₂CubeOfNat 4 15) *
          walshCharacterSum a maitraKavutYucelPointsTwo9 := by
  have hnodup : MaitraKavutYucel.flipPointList13.Nodup := by decide
  have h4667 : f₂CubeOfNat 13 4667 =
      Fin.append (f₂CubeOfNat 9 59) (f₂CubeOfNat 4 9) := by decide
  have h4758 : f₂CubeOfNat 13 4758 =
      Fin.append (f₂CubeOfNat 9 150) (f₂CubeOfNat 4 9) := by decide
  have h4807 : f₂CubeOfNat 13 4807 =
      Fin.append (f₂CubeOfNat 9 199) (f₂CubeOfNat 4 9) := by decide
  have h4823 : f₂CubeOfNat 13 4823 =
      Fin.append (f₂CubeOfNat 9 215) (f₂CubeOfNat 4 9) := by decide
  have h4913 : f₂CubeOfNat 13 4913 =
      Fin.append (f₂CubeOfNat 9 305) (f₂CubeOfNat 4 9) := by decide
  have h5042 : f₂CubeOfNat 13 5042 =
      Fin.append (f₂CubeOfNat 9 434) (f₂CubeOfNat 4 9) := by decide
  have h8133 : f₂CubeOfNat 13 8133 =
      Fin.append (f₂CubeOfNat 9 453) (f₂CubeOfNat 4 15) := by decide
  have h8187 : f₂CubeOfNat 13 8187 =
      Fin.append (f₂CubeOfNat 9 507) (f₂CubeOfNat 4 15) := by decide
  rw [show (∑ p ∈ MaitraKavutYucel.flipPoints13,
      walshCharacterInt (Fin.append a b) p) =
      (MaitraKavutYucel.flipPointList13.map
        (walshCharacterInt (Fin.append a b))).sum by
    exact List.sum_toFinset _ hnodup]
  simp [MaitraKavutYucel.flipPointList13, h4667, h4758, h4807, h4823,
    h4913, h5042, h8133, h8187, walshCharacterInt_append,
    walshCharacterSum, maitraKavutYucelPointsSix9, maitraKavutYucelPointsTwo9]
  ring

private theorem maitraKavutYucelFlipWalshTermSum
    (a : FABL.F₂Cube 9) (b : FABL.F₂Cube 4) :
    (∑ p ∈ MaitraKavutYucel.flipPoints13,
        walshTerm MaitraKavutYucel.initialFunction13 (Fin.append a b) p) =
      walshCharacterInt b (f₂CubeOfNat 4 9) *
          walshCharacterSum a maitraKavutYucelPointsSix9 +
        walshCharacterInt b (f₂CubeOfNat 4 15) *
          walshCharacterSum a maitraKavutYucelPointsTwo9 := by
  calc
    (∑ p ∈ MaitraKavutYucel.flipPoints13,
        walshTerm MaitraKavutYucel.initialFunction13 (Fin.append a b) p) =
        ∑ p ∈ MaitraKavutYucel.flipPoints13,
          walshCharacterInt (Fin.append a b) p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact maitraKavutYucelFlipWalshTerm_eq_character (Fin.append a b) p hp
    _ = _ := maitraKavutYucelFlipCharacterSum a b

private theorem walshTransform_maitraKavutYucelFunction13_append
    (a : FABL.F₂Cube 9) (b : FABL.F₂Cube 4) :
    walshTransform maitraKavutYucelFunction13 (Fin.append a b) =
      walshTransform MaitraKavutYucel.shiftedSeedFunction9 a *
          walshTransform MaitraKavutYucel.bentFunction4 b -
        2 * (walshCharacterInt b (f₂CubeOfNat 4 9) *
            walshCharacterSum a maitraKavutYucelPointsSix9 +
          walshCharacterInt b (f₂CubeOfNat 4 15) *
            walshCharacterSum a maitraKavutYucelPointsTwo9) := by
  rw [maitraKavutYucelFunction13, maitraKavutYucelWalshTransform_flipOn,
    maitraKavutYucelFlipWalshTermSum, MaitraKavutYucel.initialFunction13,
    walshTransform_booleanDirectSum_append]

private theorem walshCharacterInt_natAbs
    {n : ℕ} (a x : FABL.F₂Cube n) :
    (walshCharacterInt a x).natAbs = 1 := by
  unfold walshCharacterInt
  generalize FABL.f₂DotProduct a x = b
  fin_cases b <;> rfl

private theorem walshCharacterSum_natAbs_le_length
    {n : ℕ} (a : FABL.F₂Cube n) (points : List (FABL.F₂Cube n)) :
    (walshCharacterSum a points).natAbs ≤ points.length := by
  unfold walshCharacterSum
  induction points with
  | nil => simp
  | cons point points ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        (walshCharacterInt a point +
            (points.map (walshCharacterInt a)).sum).natAbs ≤
            (walshCharacterInt a point).natAbs +
              ((points.map (walshCharacterInt a)).sum).natAbs :=
          Int.natAbs_add_le _ _
        _ = 1 + ((points.map (walshCharacterInt a)).sum).natAbs := by
          rw [walshCharacterInt_natAbs]
        _ ≤ 1 + points.length := Nat.add_le_add_left ih 1
        _ = points.length + 1 := by omega

private theorem maitraKavutYucelBitSignCombination_natAbs_le
    (u v : FABL.𝔽₂) (s t : ℤ)
    (hplus : (s + t).natAbs ≤ 4)
    (hminus : (s - t).natAbs ≤ 4) :
    (bitSignInt u * s + bitSignInt v * t).natAbs ≤ 4 := by
  by_cases hu : u = 0
  · subst u
    by_cases hv : v = 0
    · subst v
      simpa [bitSignInt] using hplus
    · have hv_one : v = 1 := Fin.eq_one_of_ne_zero v hv
      subst v
      simpa [sub_eq_add_neg, bitSignInt] using hminus
  · have hu_one : u = 1 := Fin.eq_one_of_ne_zero u hu
    subst u
    by_cases hv : v = 0
    · subst v
      rw [show bitSignInt 1 * s + bitSignInt 0 * t = -(s - t) by
          simp [bitSignInt]
          ring,
        Int.natAbs_neg]
      exact hminus
    · have hv_one : v = 1 := Fin.eq_one_of_ne_zero v hv
      subst v
      rw [show bitSignInt 1 * s + bitSignInt 1 * t = -(s + t) by
          simp [bitSignInt]
          ring,
        Int.natAbs_neg]
      exact hplus

private theorem walshCharacterIntCombination_natAbs_le
    (b : FABL.F₂Cube 4) (s t : ℤ)
    (hplus : (s + t).natAbs ≤ 4)
    (hminus : (s - t).natAbs ≤ 4) :
    (walshCharacterInt b (f₂CubeOfNat 4 9) * s +
        walshCharacterInt b (f₂CubeOfNat 4 15) * t).natAbs ≤ 4 := by
  exact maitraKavutYucelBitSignCombination_natAbs_le
    (FABL.f₂DotProduct b (f₂CubeOfNat 4 9))
    (FABL.f₂DotProduct b (f₂CubeOfNat 4 15)) s t hplus hminus

private theorem maitraKavutYucelFlipCorrection_natAbs_le_eight
    (a : FABL.F₂Cube 9) (b : FABL.F₂Cube 4) :
    (walshCharacterInt b (f₂CubeOfNat 4 9) *
          walshCharacterSum a maitraKavutYucelPointsSix9 +
        walshCharacterInt b (f₂CubeOfNat 4 15) *
          walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs ≤ 8 := by
  calc
    (walshCharacterInt b (f₂CubeOfNat 4 9) *
          walshCharacterSum a maitraKavutYucelPointsSix9 +
        walshCharacterInt b (f₂CubeOfNat 4 15) *
          walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs ≤
        (walshCharacterInt b (f₂CubeOfNat 4 9) *
          walshCharacterSum a maitraKavutYucelPointsSix9).natAbs +
        (walshCharacterInt b (f₂CubeOfNat 4 15) *
          walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs :=
      Int.natAbs_add_le _ _
    _ = (walshCharacterSum a maitraKavutYucelPointsSix9).natAbs +
        (walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs := by
      simp [Int.natAbs_mul, walshCharacterInt_natAbs]
    _ ≤ maitraKavutYucelPointsSix9.length + maitraKavutYucelPointsTwo9.length :=
      Nat.add_le_add
        (walshCharacterSum_natAbs_le_length a maitraKavutYucelPointsSix9)
        (walshCharacterSum_natAbs_le_length a maitraKavutYucelPointsTwo9)
    _ = 8 := by decide

private theorem maitraKavutYucelFunction13_walsh_bound_append
    (a : FABL.F₂Cube 9) (b : FABL.F₂Cube 4) :
    (walshTransform maitraKavutYucelFunction13 (Fin.append a b)).natAbs ≤ 120 := by
  rw [walshTransform_maitraKavutYucelFunction13_append]
  have hb := maitraKavutYucelBentSpectrum b
  rcases maitraKavutYucelSeedSpectrum a with hsmall | ⟨hmax, hplus, hminus⟩
  · have hcorrection := maitraKavutYucelFlipCorrection_natAbs_le_eight a b
    calc
      (walshTransform MaitraKavutYucel.shiftedSeedFunction9 a *
            walshTransform MaitraKavutYucel.bentFunction4 b -
          2 * (walshCharacterInt b (f₂CubeOfNat 4 9) *
                walshCharacterSum a maitraKavutYucelPointsSix9 +
              walshCharacterInt b (f₂CubeOfNat 4 15) *
                walshCharacterSum a maitraKavutYucelPointsTwo9)).natAbs ≤
          (walshTransform MaitraKavutYucel.shiftedSeedFunction9 a *
            walshTransform MaitraKavutYucel.bentFunction4 b).natAbs +
          (2 * (walshCharacterInt b (f₂CubeOfNat 4 9) *
                walshCharacterSum a maitraKavutYucelPointsSix9 +
              walshCharacterInt b (f₂CubeOfNat 4 15) *
                walshCharacterSum a maitraKavutYucelPointsTwo9)).natAbs :=
        Int.natAbs_sub_le _ _
      _ = (walshTransform MaitraKavutYucel.shiftedSeedFunction9 a).natAbs * 4 +
          2 * (walshCharacterInt b (f₂CubeOfNat 4 9) *
                walshCharacterSum a maitraKavutYucelPointsSix9 +
              walshCharacterInt b (f₂CubeOfNat 4 15) *
                walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_mul, hb]
        norm_num
      _ ≤ 120 := by omega
  · have hcorrection := walshCharacterIntCombination_natAbs_le b
      (walshCharacterSum a maitraKavutYucelPointsSix9)
      (walshCharacterSum a maitraKavutYucelPointsTwo9) hplus hminus
    calc
      (walshTransform MaitraKavutYucel.shiftedSeedFunction9 a *
            walshTransform MaitraKavutYucel.bentFunction4 b -
          2 * (walshCharacterInt b (f₂CubeOfNat 4 9) *
                walshCharacterSum a maitraKavutYucelPointsSix9 +
              walshCharacterInt b (f₂CubeOfNat 4 15) *
                walshCharacterSum a maitraKavutYucelPointsTwo9)).natAbs ≤
          (walshTransform MaitraKavutYucel.shiftedSeedFunction9 a *
            walshTransform MaitraKavutYucel.bentFunction4 b).natAbs +
          (2 * (walshCharacterInt b (f₂CubeOfNat 4 9) *
                walshCharacterSum a maitraKavutYucelPointsSix9 +
              walshCharacterInt b (f₂CubeOfNat 4 15) *
                walshCharacterSum a maitraKavutYucelPointsTwo9)).natAbs :=
        Int.natAbs_sub_le _ _
      _ = (walshTransform MaitraKavutYucel.shiftedSeedFunction9 a).natAbs * 4 +
          2 * (walshCharacterInt b (f₂CubeOfNat 4 9) *
                walshCharacterSum a maitraKavutYucelPointsSix9 +
              walshCharacterInt b (f₂CubeOfNat 4 15) *
                walshCharacterSum a maitraKavutYucelPointsTwo9).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_mul, hb]
        norm_num
      _ ≤ 120 := by omega

theorem maitraKavutYucelFunction13_walsh_bound
    (frequency : FABL.F₂Cube (9 + 4)) :
    (walshTransform maitraKavutYucelFunction13 frequency).natAbs ≤ 120 := by
  let p := (Fin.appendEquiv 9 4).symm frequency
  have hfrequency : Fin.append p.1 p.2 = frequency :=
    (Fin.appendEquiv 9 4).apply_symm_apply frequency
  rw [← hfrequency]
  exact maitraKavutYucelFunction13_walsh_bound_append p.1 p.2

private theorem maitraKavutYucelSeedZero_certificate :
    (fastWalshCertificateTree 9 MaitraKavutYucel.shiftedSeedFunction9).eval 0 = 4 := by
  decide

private theorem maitraKavutYucelSeedZero :
    walshTransform MaitraKavutYucel.shiftedSeedFunction9 0 = 4 := by
  rw [← fastWalshCertificateTree_correct]
  exact maitraKavutYucelSeedZero_certificate

private theorem maitraKavutYucelBentZero_certificate :
    (fastWalshCertificateTree 4 MaitraKavutYucel.bentFunction4).eval 0 = 4 := by
  decide

private theorem maitraKavutYucelBentZero :
    walshTransform MaitraKavutYucel.bentFunction4 0 = 4 := by
  rw [← fastWalshCertificateTree_correct]
  exact maitraKavutYucelBentZero_certificate

private theorem walshCharacterIntZeroAtNine :
    walshCharacterInt (0 : FABL.F₂Cube 4) (f₂CubeOfNat 4 9) = 1 := by
  decide

private theorem walshCharacterIntZeroAtFifteen :
    walshCharacterInt (0 : FABL.F₂Cube 4) (f₂CubeOfNat 4 15) = 1 := by
  decide

private theorem walshCharacterSumZeroSix :
    walshCharacterSum (0 : FABL.F₂Cube 9) maitraKavutYucelPointsSix9 = 6 := by
  decide

private theorem walshCharacterSumZeroTwo :
    walshCharacterSum (0 : FABL.F₂Cube 9) maitraKavutYucelPointsTwo9 = 2 := by
  decide

private theorem walshCharacterSumWitnessSix :
    walshCharacterSum (f₂CubeOfNat 9 1) maitraKavutYucelPointsSix9 = -2 := by
  decide

private theorem walshCharacterSumWitnessTwo :
    walshCharacterSum (f₂CubeOfNat 9 1) maitraKavutYucelPointsTwo9 = -2 := by
  decide

private theorem maitraKavutYucelFunction13_zero :
    walshTransform maitraKavutYucelFunction13 0 = 0 := by
  have happend : Fin.append (0 : FABL.F₂Cube 9) (0 : FABL.F₂Cube 4) =
      (0 : FABL.F₂Cube (9 + 4)) := by
    funext i
    refine Fin.addCases (fun l ↦ ?_) (fun r ↦ ?_) i <;> simp
  rw [← happend, walshTransform_maitraKavutYucelFunction13_append,
    maitraKavutYucelSeedZero, maitraKavutYucelBentZero, walshCharacterIntZeroAtNine,
    walshCharacterIntZeroAtFifteen, walshCharacterSumZeroSix,
    walshCharacterSumZeroTwo]
  norm_num

theorem isBalanced_maitraKavutYucelFunction13 :
    IsBalanced maitraKavutYucelFunction13 := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero]
  exact maitraKavutYucelFunction13_zero

private theorem maitraKavutYucelSeedWitness_certificate :
    (fastWalshCertificateTree 9 MaitraKavutYucel.shiftedSeedFunction9).eval
      (f₂CubeOfNat 9 1) = 28 := by
  decide

private theorem maitraKavutYucelSeedWitness :
    walshTransform MaitraKavutYucel.shiftedSeedFunction9
      (f₂CubeOfNat 9 1) = 28 := by
  rw [← fastWalshCertificateTree_correct]
  exact maitraKavutYucelSeedWitness_certificate

theorem maitraKavutYucelFunction13_walsh_witness :
    walshTransform maitraKavutYucelFunction13 (f₂CubeOfNat 13 1) = 120 := by
  have hfrequency : f₂CubeOfNat 13 1 =
      Fin.append (f₂CubeOfNat 9 1) (0 : FABL.F₂Cube 4) := by decide
  rw [hfrequency, walshTransform_maitraKavutYucelFunction13_append,
    maitraKavutYucelSeedWitness, maitraKavutYucelBentZero, walshCharacterIntZeroAtNine,
    walshCharacterIntZeroAtFifteen, walshCharacterSumWitnessSix,
    walshCharacterSumWitnessTwo]
  norm_num

theorem maxWalshMagnitude_maitraKavutYucelFunction13 :
    maxWalshMagnitude maitraKavutYucelFunction13 = 120 := by
  apply Nat.le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty
      (fun frequency : FABL.F₂Cube (9 + 4) ↦
        (walshTransform maitraKavutYucelFunction13 frequency).natAbs)
      fun frequency _hfrequency ↦
        maitraKavutYucelFunction13_walsh_bound frequency
  · have hwitness := Finset.le_sup'
      (fun frequency : FABL.F₂Cube (9 + 4) ↦
        (walshTransform maitraKavutYucelFunction13 frequency).natAbs)
      (Finset.mem_univ (f₂CubeOfNat 13 1))
    simpa [maxWalshMagnitude,
      maitraKavutYucelFunction13_walsh_witness] using hwitness

theorem nonlinearity_maitraKavutYucelFunction13 :
    nonlinearity maitraKavutYucelFunction13 = 4036 := by
  have h := two_mul_nonlinearity_add_maxWalshMagnitude
    maitraKavutYucelFunction13
  rw [maxWalshMagnitude_maitraKavutYucelFunction13] at h
  norm_num at h ⊢
  omega

/-- Extend the balanced Maitra--Kavut--Yücel seed by a complete bent block. -/
def maitraKavutYucelBentExtension (m : ℕ) :
    BooleanFunction (13 + (m + m)) :=
  completeBentExtension maitraKavutYucelFunction13 m

/-- Every complete bent extension of the Maitra--Kavut--Yücel seed is balanced. -/
theorem isBalanced_maitraKavutYucelBentExtension (m : ℕ) :
    IsBalanced (maitraKavutYucelBentExtension m) := by
  exact isBalanced_completeBentExtension maitraKavutYucelFunction13 m
    isBalanced_maitraKavutYucelFunction13

/-- The extended balanced family has maximum Walsh magnitude `120 * 2^m`. -/
theorem maxWalshMagnitude_maitraKavutYucelBentExtension (m : ℕ) :
    maxWalshMagnitude (maitraKavutYucelBentExtension m) = 120 * 2 ^ m := by
  rw [maitraKavutYucelBentExtension,
    maxWalshMagnitude_completeBentExtension,
    maxWalshMagnitude_maitraKavutYucelFunction13]

/-- The extended balanced family has nonlinearity
`2^(12+2m) - 60 * 2^m`. -/
theorem nonlinearity_maitraKavutYucelBentExtension (m : ℕ) :
    nonlinearity (maitraKavutYucelBentExtension m) =
      2 ^ (12 + (m + m)) - 60 * 2 ^ m := by
  have h := two_mul_nonlinearity_add_maxWalshMagnitude
    (maitraKavutYucelBentExtension m)
  rw [maxWalshMagnitude_maitraKavutYucelBentExtension] at h
  have hpow : 2 ^ (13 + (m + m)) = 2 * 2 ^ (12 + (m + m)) := by
    rw [show 13 + (m + m) = (12 + (m + m)) + 1 by omega, pow_succ]
    ring
  rw [hpow] at h
  omega

/-- Every member of the balanced family strictly exceeds the odd-dimensional
quadratic nonlinearity bound. -/
theorem quadraticBound_lt_nonlinearity_maitraKavutYucelBentExtension
    (m : ℕ) :
    2 ^ (12 + (m + m)) - 2 ^ (6 + m) <
      nonlinearity (maitraKavutYucelBentExtension m) := by
  rw [nonlinearity_maitraKavutYucelBentExtension]
  have hsmall : 60 * 2 ^ m < 64 * 2 ^ m := by
    have hpositive : 0 < 2 ^ m := Nat.pow_pos (by omega)
    omega
  have hsix : 2 ^ (6 + m) = 64 * 2 ^ m := by
    rw [pow_add]
    norm_num
  have hlarge : 64 * 2 ^ m ≤ 2 ^ (12 + (m + m)) := by
    rw [← hsix]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  rw [hsix]
  exact Nat.sub_lt_sub_left (hsmall.trans_le hlarge) hsmall

/-- In every odd dimension at least thirteen, a balanced Boolean function
strictly exceeds the quadratic nonlinearity bound. -/
theorem exists_isBalanced_nonlinearity_gt_quadraticBound_of_odd
    (hn : Odd n) (hn13 : 13 ≤ n) :
    ∃ f : BooleanFunction n, IsBalanced f ∧
      2 ^ (n - 1) - 2 ^ ((n - 1) / 2) < nonlinearity f := by
  obtain ⟨k, hk⟩ := hn
  have hk6 : 6 ≤ k := by omega
  let m := k - 6
  have hnform : n = 13 + (m + m) := by
    dsimp [m]
    omega
  rw [hnform]
  refine ⟨maitraKavutYucelBentExtension m,
    isBalanced_maitraKavutYucelBentExtension m, ?_⟩
  have hsub : 13 + (m + m) - 1 = 12 + (m + m) := by omega
  have hhalf : (12 + (m + m)) / 2 = 6 + m := by omega
  simpa only [hsub, hhalf] using
    quadraticBound_lt_nonlinearity_maitraKavutYucelBentExtension m

private theorem hammingWeight_add_add_two_mul_card_inter
    (f g : BooleanFunction n) :
    hammingWeight (f + g) + 2 * (support f ∩ support g).card =
      hammingWeight f + hammingWeight g := by
  classical
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support,
    hammingWeight_eq_card_support]
  have hinter :
      support f ∩ support g =
        Finset.univ.filter fun x : FABL.F₂Cube n ↦ f x = 1 ∧ g x = 1 := by
    ext x
    simp [mem_support]
  rw [hinter]
  simp only [support, FABL.f₂OneSupport, Pi.add_apply]
  simp only [Finset.card_filter]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hfx : f x = 0
  · by_cases hgx : g x = 0
    · norm_num [hfx, hgx]
    · have hgx_one : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      norm_num [hfx, hgx_one]
  · have hfx_one : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
    by_cases hgx : g x = 0
    · norm_num [hfx_one, hgx]
    · have hgx_one : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      norm_num [hfx_one, hgx_one]

private theorem four_dvd_hammingWeight_affineFunction_six
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    4 ∣ hammingWeight (FABL.affineFunction b a) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      have hzero :
          FABL.affineFunction (0 : FABL.𝔽₂) (0 : FABL.F₂Cube 6) = 0 := by
        funext x
        simp [FABL.affineFunction, FABL.f₂DotProduct]
      rw [hzero]
      simp
    · have hb_one : b = 1 := Fin.eq_one_of_ne_zero _ hb
      subst b
      rw [hammingWeight_affineFunction_one_zero]
      norm_num
  · rw [hammingWeight_affineFunction_of_ne_zero b a ha]
    norm_num

private theorem even_support_inter_affineFunction_of_degree_le_four
    (f : BooleanFunction 6) (hf : FABL.functionAlgebraicDegree f ≤ 4)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    Even (support f ∩ support (FABL.affineFunction b a)).card := by
  have hfmem : f ∈ reedMuller 4 6 := hf
  have hfdual : f ∈ reedMullerDual 1 6 := by
    rw [reedMullerDual_eq (r := 1) (n := 6) (by omega)]
    norm_num
    exact hfmem
  rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff] at hfdual
  have hpair := hfdual (FABL.affineFunction b a)
    (affineFunction_mem_reedMuller_one b a)
  exact even_card_support_inter_of_pairing_eq_zero f
    (FABL.affineFunction b a) (by
      rw [booleanFunctionPairing_apply]
      calc
        ∑ x, f x * FABL.affineFunction b a x =
            ∑ x, FABL.affineFunction b a x * f x := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact mul_comm _ _
        _ = 0 := hpair)

private theorem hammingDistance_affineFunction_mod_four_eq_weight_mod_four
    (f : BooleanFunction 6) (hf : FABL.functionAlgebraicDegree f ≤ 4)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    hammingDistance f (FABL.affineFunction b a) % 4 = hammingWeight f % 4 := by
  rw [hammingDistance_eq_hammingWeight_add]
  have hidentity := hammingWeight_add_add_two_mul_card_inter f
    (FABL.affineFunction b a)
  obtain ⟨k, hk⟩ :=
    even_support_inter_affineFunction_of_degree_le_four f hf b a
  obtain ⟨q, hq⟩ := four_dvd_hammingWeight_affineFunction_six b a
  omega

private theorem exists_affineFunction_hammingDistance_eq_nonlinearity
    (f : BooleanFunction n) :
    ∃ b a, hammingDistance f (FABL.affineFunction b a) = nonlinearity f := by
  classical
  unfold nonlinearity
  obtain ⟨p, _hp, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)))
    Finset.univ_nonempty
    (fun q ↦ hammingDistance f (FABL.affineFunction q.1 q.2))
  exact ⟨p.1, p.2, hmin.symm⟩

private theorem walshTransform_eq_sixty_four_sub_two_mul_distance
    (f : BooleanFunction 6) (a : FABL.F₂Cube 6) :
    walshTransform f a =
      64 - 2 * (hammingDistance f (FABL.affineFunction 0 a) : ℤ) := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℝ)))
  push_cast
  have hdistance := hammingDistance_cast_linearFunction_eq f a
  norm_num at hdistance ⊢
  linarith

private theorem natAbs_walshTransform_eq_four_or_twelve_of_degree_le_four
    (f : BooleanFunction 6) (hdegree : FABL.functionAlgebraicDegree f ≤ 4)
    (hf : nonlinearity f = 26) (a : FABL.F₂Cube 6) :
    (walshTransform f a).natAbs = 4 ∨
      (walshTransform f a).natAbs = 12 := by
  obtain ⟨bmin, amin, hmin⟩ :=
    exists_affineFunction_hammingDistance_eq_nonlinearity f
  have hminimumMod :=
    hammingDistance_affineFunction_mod_four_eq_weight_mod_four
      f hdegree bmin amin
  rw [hmin, hf] at hminimumMod
  norm_num at hminimumMod
  have hlinearMod :=
    hammingDistance_affineFunction_mod_four_eq_weight_mod_four
      f hdegree 0 a
  have hdistanceMod :
      hammingDistance f (FABL.affineFunction 0 a) % 4 = 2 := by
    omega
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  rw [hf] at hrelation
  norm_num at hrelation
  have hmaximum : maxWalshMagnitude f = 12 := by omega
  have hbound : (walshTransform f a).natAbs ≤ 12 := by
    have hle := Finset.le_sup'
      (fun u : FABL.F₂Cube 6 ↦ (walshTransform f u).natAbs)
      (Finset.mem_univ a)
    change (walshTransform f a).natAbs ≤ maxWalshMagnitude f at hle
    rwa [hmaximum] at hle
  have hwalsh := walshTransform_eq_sixty_four_sub_two_mul_distance f a
  rcases Int.natAbs_eq (walshTransform f a) with hpositive | hnegative
  · rw [hpositive] at hwalsh
    omega
  · rw [hnegative] at hwalsh
    omega

private theorem card_walshTransform_natAbs_eq_twelve_of_degree_le_four
    (f : BooleanFunction 6) (hdegree : FABL.functionAlgebraicDegree f ≤ 4)
    (hf : nonlinearity f = 26) :
    ((Finset.univ : Finset (FABL.F₂Cube 6)).filter
      fun a ↦ (walshTransform f a).natAbs = 12).card = 24 := by
  let high := (Finset.univ : Finset (FABL.F₂Cube 6)).filter
    fun a ↦ (walshTransform f a).natAbs = 12
  let low := (Finset.univ : Finset (FABL.F₂Cube 6)).filter
    fun a ↦ ¬(walshTransform f a).natAbs = 12
  have hparsevalReal := sum_walshTransform_sq_eq_two_pow_sq f
  have hparseval :
      ∑ a : FABL.F₂Cube 6, walshTransform f a ^ 2 = (4096 : ℤ) := by
    apply (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℝ)))
    push_cast
    norm_num at hparsevalReal ⊢
    exact hparsevalReal
  have hsquareHigh (a : FABL.F₂Cube 6)
      (ha : (walshTransform f a).natAbs = 12) :
      walshTransform f a ^ 2 = (144 : ℤ) := by
    rcases Int.natAbs_eq (walshTransform f a) with hpositive | hnegative
    · rw [ha] at hpositive
      rw [hpositive]
      norm_num
    · rw [ha] at hnegative
      rw [hnegative]
      norm_num
  have hsquareLow (a : FABL.F₂Cube 6)
      (ha : ¬(walshTransform f a).natAbs = 12) :
      walshTransform f a ^ 2 = (16 : ℤ) := by
    rcases natAbs_walshTransform_eq_four_or_twelve_of_degree_le_four
      f hdegree hf a with hfour | htwelve
    · rcases Int.natAbs_eq (walshTransform f a) with hpositive | hnegative
      · rw [hfour] at hpositive
        rw [hpositive]
        norm_num
      · rw [hfour] at hnegative
        rw [hnegative]
        norm_num
    · exact False.elim (ha htwelve)
  have hsumHigh :
      ∑ a ∈ high, walshTransform f a ^ 2 = (high.card : ℤ) * 144 := by
    calc
      ∑ a ∈ high, walshTransform f a ^ 2 = ∑ _a ∈ high, (144 : ℤ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hsquareHigh a (by simpa [high] using ha)
      _ = (high.card : ℤ) * 144 := by simp
  have hsumLow :
      ∑ a ∈ low, walshTransform f a ^ 2 = (low.card : ℤ) * 16 := by
    calc
      ∑ a ∈ low, walshTransform f a ^ 2 = ∑ _a ∈ low, (16 : ℤ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hsquareLow a (by simpa [low] using ha)
      _ = (low.card : ℤ) * 16 := by simp
  have hsplitSum := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (FABL.F₂Cube 6))
    (fun a ↦ (walshTransform f a).natAbs = 12)
    (fun a ↦ walshTransform f a ^ 2)
  change (∑ a ∈ high, walshTransform f a ^ 2) +
      (∑ a ∈ low, walshTransform f a ^ 2) =
        ∑ a : FABL.F₂Cube 6, walshTransform f a ^ 2 at hsplitSum
  rw [hsumHigh, hsumLow, hparseval] at hsplitSum
  have hsplitCard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (FABL.F₂Cube 6)))
    (fun a : FABL.F₂Cube 6 ↦ (walshTransform f a).natAbs = 12)
  change high.card + low.card = Fintype.card (FABL.F₂Cube 6) at hsplitCard
  rw [card_f₂Cube] at hsplitCard
  norm_num at hsplitCard
  change high.card = 24
  omega

private theorem sum_walshTransform_mul_walshTerm_eq_two_pow
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    ∑ a, walshTransform f a * walshTerm f a x = (2 ^ n : ℤ) := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℝ)))
  push_cast
  calc
    ∑ a, (walshTransform f a : ℝ) * (walshTerm f a x : ℝ) =
        realSignView f x *
          ∑ a, (walshTransform f a : ℝ) * FABL.vectorWalshCharacter a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [walshTerm_cast_eq_realSignView_mul_character]
      ring
    _ = realSignView f x * ((2 : ℝ) ^ n * realSignView f x) := by
      rw [two_pow_mul_realSignView_eq_sum_walshTransform_mul_character]
    _ = (2 : ℝ) ^ n := by
      calc
        realSignView f x * ((2 : ℝ) ^ n * realSignView f x) =
            (2 : ℝ) ^ n * (realSignView f x * realSignView f x) := by ring
        _ = (2 : ℝ) ^ n := by rw [realSignView_mul_self]; ring

private theorem walshTerm_eq_one_or_neg_one
    (f : BooleanFunction n) (a x : FABL.F₂Cube n) :
    walshTerm f a x = 1 ∨ walshTerm f a x = -1 := by
  rw [walshTerm, bitSignInt_eq_if_one]
  split <;> simp

private theorem natAbs_walshTransform_eq_eight_of_nonlinearity_eq_28
    (f : BooleanFunction 6) (hf : nonlinearity f = 28)
    (a : FABL.F₂Cube 6) :
    (walshTransform f a).natAbs = 8 := by
  have hcover :
      (nonlinearity f : ℝ) =
        (2 : ℝ) ^ 6 / 2 - Real.sqrt ((2 : ℝ) ^ 6) / 2 := by
    rw [hf]
    norm_num
  have hflat :=
    (nonlinearity_eq_coveringRadius_iff_flatWalshSpectrum f).mp hcover a
  norm_num at hflat
  have hcast : ((walshTransform f a).natAbs : ℝ) = 8 := by
    simpa using hflat
  exact_mod_cast hcast

/-- A six-variable coset at covering radius has, through every coordinate,
a minimum-weight representative modulo the first-order Reed--Muller code. -/
theorem exists_minimum_affine_error_one_at_of_nonlinearity_eq_28
    (f : BooleanFunction 6) (hf : nonlinearity f = 28)
    (x : FABL.F₂Cube 6) :
    ∃ b a, hammingDistance f (FABL.affineFunction b a) = 28 ∧
      (f + FABL.affineFunction b a) x = 1 := by
  have hinversion := sum_walshTransform_mul_walshTerm_eq_two_pow f x
  have hexists :
      ∃ a : FABL.F₂Cube 6,
        walshTransform f a * walshTerm f a x = -8 := by
    by_contra hnone
    push Not at hnone
    have hproduct (a : FABL.F₂Cube 6) :
        walshTransform f a * walshTerm f a x = 8 := by
      have hne := hnone a
      have habs := natAbs_walshTransform_eq_eight_of_nonlinearity_eq_28 f hf a
      rcases Int.natAbs_eq (walshTransform f a) with hwalsh | hwalsh
      · rw [habs] at hwalsh
        rcases walshTerm_eq_one_or_neg_one f a x with hterm | hterm
        · rw [hwalsh, hterm]
          norm_num
        · exfalso
          apply hne
          rw [hwalsh, hterm]
          norm_num
      · rw [habs] at hwalsh
        rcases walshTerm_eq_one_or_neg_one f a x with hterm | hterm
        · exfalso
          apply hne
          rw [hwalsh, hterm]
          norm_num
        · rw [hwalsh, hterm]
          norm_num
    simp_rw [hproduct] at hinversion
    norm_num at hinversion
  obtain ⟨a, ha⟩ := hexists
  have habs := natAbs_walshTransform_eq_eight_of_nonlinearity_eq_28 f hf a
  rcases Int.natAbs_eq (walshTransform f a) with hwalsh | hwalsh <;>
    rw [habs] at hwalsh
  · refine ⟨0, a, ?_, ?_⟩
    · have hdistance := hammingDistance_cast_linearFunction_eq f a
      rw [hwalsh] at hdistance
      norm_num at hdistance
      exact_mod_cast hdistance
    · rw [hwalsh] at ha
      have hterm : walshTerm f a x = -1 := by omega
      have hbit : f x + FABL.f₂DotProduct a x = 1 := by
        by_contra hne
        have hzero : f x + FABL.f₂DotProduct a x = 0 := by
          by_contra hnz
          exact hne (Fin.eq_one_of_ne_zero _ hnz)
        rw [walshTerm, bitSignInt_eq_if_one, if_neg (by simp [hzero])] at hterm
        omega
      change f x + (0 + FABL.f₂DotProduct a x) = 1
      simpa using hbit
  · refine ⟨1, a, ?_, ?_⟩
    · have hdistance := hammingDistance_cast_affineFunction_eq f 1 a
      rw [hwalsh] at hdistance
      norm_num [bitSignInt] at hdistance
      exact_mod_cast hdistance
    · rw [hwalsh] at ha
      have hterm : walshTerm f a x = 1 := by omega
      have hbit : f x + FABL.f₂DotProduct a x = 0 := by
        by_contra hne
        have hone : f x + FABL.f₂DotProduct a x = 1 :=
          Fin.eq_one_of_ne_zero _ hne
        rw [walshTerm, bitSignInt_eq_if_one, if_pos hone] at hterm
        omega
      change f x + (1 + FABL.f₂DotProduct a x) = 1
      calc
        f x + (1 + FABL.f₂DotProduct a x) =
            1 + (f x + FABL.f₂DotProduct a x) := by ac_rfl
        _ = 1 := by rw [hbit]; simp

/-- A degree-at-most-four six-variable coset of nonlinearity `26` has,
through every coordinate, a minimum-weight representative modulo the
first-order Reed--Muller code. -/
theorem exists_minimum_affine_error_one_at_of_degree_le_four_nonlinearity_eq_26
    (f : BooleanFunction 6) (hdegree : FABL.functionAlgebraicDegree f ≤ 4)
    (hf : nonlinearity f = 26) (x : FABL.F₂Cube 6) :
    ∃ b a, hammingDistance f (FABL.affineFunction b a) = 26 ∧
      (f + FABL.affineFunction b a) x = 1 := by
  let high := (Finset.univ : Finset (FABL.F₂Cube 6)).filter
    fun a ↦ (walshTransform f a).natAbs = 12
  let low := (Finset.univ : Finset (FABL.F₂Cube 6)).filter
    fun a ↦ ¬(walshTransform f a).natAbs = 12
  have hhighCard : high.card = 24 := by
    simpa [high] using
      card_walshTransform_natAbs_eq_twelve_of_degree_le_four f hdegree hf
  have hcardSplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (FABL.F₂Cube 6)))
    (fun a : FABL.F₂Cube 6 ↦ (walshTransform f a).natAbs = 12)
  change high.card + low.card = Fintype.card (FABL.F₂Cube 6) at hcardSplit
  rw [card_f₂Cube] at hcardSplit
  norm_num at hcardSplit
  have hlowCard : low.card = 40 := by omega
  have hinversion := sum_walshTransform_mul_walshTerm_eq_two_pow f x
  have hexists :
      ∃ a : FABL.F₂Cube 6,
        (walshTransform f a).natAbs = 12 ∧
          walshTransform f a * walshTerm f a x = -12 := by
    by_contra hnone
    push Not at hnone
    have hhighProduct (a : FABL.F₂Cube 6)
        (ha : (walshTransform f a).natAbs = 12) :
        walshTransform f a * walshTerm f a x = 12 := by
      have hne := hnone a ha
      rcases Int.natAbs_eq (walshTransform f a) with hwalsh | hwalsh
      · rw [ha] at hwalsh
        rcases walshTerm_eq_one_or_neg_one f a x with hterm | hterm
        · rw [hwalsh, hterm]
          norm_num
        · exfalso
          apply hne
          rw [hwalsh, hterm]
          norm_num
      · rw [ha] at hwalsh
        rcases walshTerm_eq_one_or_neg_one f a x with hterm | hterm
        · exfalso
          apply hne
          rw [hwalsh, hterm]
          norm_num
        · rw [hwalsh, hterm]
          norm_num
    have hlowProduct (a : FABL.F₂Cube 6)
        (ha : ¬(walshTransform f a).natAbs = 12) :
        (-4 : ℤ) ≤ walshTransform f a * walshTerm f a x := by
      rcases natAbs_walshTransform_eq_four_or_twelve_of_degree_le_four
        f hdegree hf a with hfour | htwelve
      · rcases Int.natAbs_eq (walshTransform f a) with hwalsh | hwalsh
        · rw [hfour] at hwalsh
          rcases walshTerm_eq_one_or_neg_one f a x with hterm | hterm <;>
            rw [hwalsh, hterm] <;> norm_num
        · rw [hfour] at hwalsh
          rcases walshTerm_eq_one_or_neg_one f a x with hterm | hterm <;>
            rw [hwalsh, hterm] <;> norm_num
      · exact False.elim (ha htwelve)
    have hsumHigh :
        ∑ a ∈ high, (if (walshTransform f a).natAbs = 12 then
          (12 : ℤ) else -4) = (high.card : ℤ) * 12 := by
      calc
        ∑ a ∈ high, (if (walshTransform f a).natAbs = 12 then
            (12 : ℤ) else -4) = ∑ _a ∈ high, (12 : ℤ) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [if_pos (by simpa [high] using ha)]
        _ = (high.card : ℤ) * 12 := by simp
    have hsumLow :
        ∑ a ∈ low, (if (walshTransform f a).natAbs = 12 then
          (12 : ℤ) else -4) = (low.card : ℤ) * (-4) := by
      calc
        ∑ a ∈ low, (if (walshTransform f a).natAbs = 12 then
            (12 : ℤ) else -4) = ∑ _a ∈ low, (-4 : ℤ) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [if_neg (by simpa [low] using ha)]
        _ = (low.card : ℤ) * (-4) := by simp
    have hbenchmarkSplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (FABL.F₂Cube 6))
      (fun a ↦ (walshTransform f a).natAbs = 12)
      (fun a ↦ if (walshTransform f a).natAbs = 12 then (12 : ℤ) else -4)
    change
      (∑ a ∈ high, (if (walshTransform f a).natAbs = 12 then
        (12 : ℤ) else -4)) +
      (∑ a ∈ low, (if (walshTransform f a).natAbs = 12 then
        (12 : ℤ) else -4)) =
      ∑ a : FABL.F₂Cube 6,
        (if (walshTransform f a).natAbs = 12 then (12 : ℤ) else -4)
      at hbenchmarkSplit
    rw [hsumHigh, hsumLow, hhighCard, hlowCard] at hbenchmarkSplit
    norm_num at hbenchmarkSplit
    have hpointwise (a : FABL.F₂Cube 6) :
        (if (walshTransform f a).natAbs = 12 then (12 : ℤ) else -4) ≤
          walshTransform f a * walshTerm f a x := by
      by_cases ha : (walshTransform f a).natAbs = 12
      · rw [if_pos ha, hhighProduct a ha]
      · rw [if_neg ha]
        exact hlowProduct a ha
    have hsumLower := Finset.sum_le_sum
      (s := (Finset.univ : Finset (FABL.F₂Cube 6)))
      (fun a _ha ↦ hpointwise a)
    change
      (∑ a : FABL.F₂Cube 6,
        (if (walshTransform f a).natAbs = 12 then (12 : ℤ) else -4)) ≤
      ∑ a : FABL.F₂Cube 6, walshTransform f a * walshTerm f a x
      at hsumLower
    rw [← hbenchmarkSplit, hinversion] at hsumLower
    norm_num at hsumLower
  obtain ⟨a, habs, ha⟩ := hexists
  rcases Int.natAbs_eq (walshTransform f a) with hwalsh | hwalsh <;>
    rw [habs] at hwalsh
  · refine ⟨0, a, ?_, ?_⟩
    · have hdistance := hammingDistance_cast_linearFunction_eq f a
      rw [hwalsh] at hdistance
      norm_num at hdistance
      exact_mod_cast hdistance
    · rw [hwalsh] at ha
      have hterm : walshTerm f a x = -1 := by omega
      have hbit : f x + FABL.f₂DotProduct a x = 1 := by
        by_contra hne
        have hzero : f x + FABL.f₂DotProduct a x = 0 := by
          by_contra hnz
          exact hne (Fin.eq_one_of_ne_zero _ hnz)
        rw [walshTerm, bitSignInt_eq_if_one, if_neg (by simp [hzero])] at hterm
        omega
      change f x + (0 + FABL.f₂DotProduct a x) = 1
      simpa using hbit
  · refine ⟨1, a, ?_, ?_⟩
    · have hdistance := hammingDistance_cast_affineFunction_eq f 1 a
      rw [hwalsh] at hdistance
      norm_num [bitSignInt] at hdistance
      exact_mod_cast hdistance
    · rw [hwalsh] at ha
      have hterm : walshTerm f a x = 1 := by omega
      have hbit : f x + FABL.f₂DotProduct a x = 0 := by
        by_contra hne
        have hone : f x + FABL.f₂DotProduct a x = 1 :=
          Fin.eq_one_of_ne_zero _ hne
        rw [walshTerm, bitSignInt_eq_if_one, if_pos hone] at hterm
        omega
      change f x + (1 + FABL.f₂DotProduct a x) = 1
      calc
        f x + (1 + FABL.f₂DotProduct a x) =
            1 + (f x + FABL.f₂DotProduct a x) := by ac_rfl
        _ = 1 := by rw [hbit]; simp

private def skewLiftSeven
    (A : Matrix (Fin 7) (Fin 7) FABL.𝔽₂) : Matrix (Fin 7) (Fin 7) ℤ :=
  fun i j ↦
    if i < j then (A i j).val
    else if j < i then -((A j i).val : ℤ)
    else 0

private theorem skewLiftSeven_transpose
    (A : Matrix (Fin 7) (Fin 7) FABL.𝔽₂) :
    (skewLiftSeven A).transpose = -(skewLiftSeven A) := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [skewLiftSeven, hij, asymm hij]
  · subst j
    simp [skewLiftSeven]
  · simp [skewLiftSeven, hij, asymm hij]

private theorem skewLiftSeven_det_eq_zero
    (A : Matrix (Fin 7) (Fin 7) FABL.𝔽₂) :
    (skewLiftSeven A).det = 0 := by
  have hneg : (-(skewLiftSeven A)).det = -(skewLiftSeven A).det := by
    rw [Matrix.det_neg]
    norm_num
  have hselfneg : (skewLiftSeven A).det = -(skewLiftSeven A).det := by
    calc
      (skewLiftSeven A).det = (skewLiftSeven A).transpose.det :=
        (Matrix.det_transpose _).symm
      _ = (-(skewLiftSeven A)).det := by rw [skewLiftSeven_transpose]
      _ = -(skewLiftSeven A).det := hneg
  linarith

private theorem map_skewLiftSeven_eq
    (A : Matrix (Fin 7) (Fin 7) FABL.𝔽₂)
    (hsymm : A.transpose = A) (hdiag : ∀ i, A i i = 0) :
    (skewLiftSeven A).map (Int.castRingHom FABL.𝔽₂) = A := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [skewLiftSeven, hij]
  · subst j
    simp [skewLiftSeven, hdiag]
  · have hsymm_apply : A j i = A i j := by
      have := congr_fun (congr_fun hsymm i) j
      simpa using this
    simp [skewLiftSeven, hij, asymm hij, hsymm_apply]

private theorem exists_nonzero_mulVec_eq_zero_of_symmetric_zero_diagonal_seven
    (A : Matrix (Fin 7) (Fin 7) FABL.𝔽₂)
    (hsymm : A.transpose = A) (hdiag : ∀ i, A i i = 0) :
    ∃ u : FABL.F₂Cube 7, u ≠ 0 ∧ A.mulVec u = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mpr
  calc
    A.det = ((skewLiftSeven A).map (Int.castRingHom FABL.𝔽₂)).det := by
      rw [map_skewLiftSeven_eq A hsymm hdiag]
    _ = Int.castRingHom FABL.𝔽₂ (skewLiftSeven A).det :=
      (RingHom.map_det _ _).symm
    _ = 0 := by rw [skewLiftSeven_det_eq_zero]; simp

private def swapZeroLinearEquiv (k : Fin 7) :
    FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7 where
  toFun x i := x (Equiv.swap 0 k i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x i := x (Equiv.swap 0 k i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

private def pivotShearLinearEquiv
    (u : FABL.F₂Cube 7) (k : Fin 7) (huk : u k = 1) :
    FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7 where
  toFun x := x + x k • (u + (Pi.single k 1 : FABL.F₂Cube 7))
  map_add' x y := by
    funext i
    simp [add_smul]
    ring
  map_smul' c x := by
    funext i
    simp [smul_add]
    ring
  invFun x := x + x k • (u + (Pi.single k 1 : FABL.F₂Cube 7))
  left_inv x := by
    have hwk : (u + (Pi.single k 1 : FABL.F₂Cube 7)) k = 0 := by simp [huk]
    funext i
    change (x i + x k * (u + (Pi.single k 1 : FABL.F₂Cube 7)) i) +
      (x k + x k * (u + (Pi.single k 1 : FABL.F₂Cube 7)) k) *
        (u + (Pi.single k 1 : FABL.F₂Cube 7)) i = x i
    rw [hwk]
    simp only [mul_zero, add_zero]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  right_inv x := by
    have hwk : (u + (Pi.single k 1 : FABL.F₂Cube 7)) k = 0 := by simp [huk]
    funext i
    change (x i + x k * (u + (Pi.single k 1 : FABL.F₂Cube 7)) i) +
      (x k + x k * (u + (Pi.single k 1 : FABL.F₂Cube 7)) k) *
        (u + (Pi.single k 1 : FABL.F₂Cube 7)) i = x i
    rw [hwk]
    simp only [mul_zero, add_zero]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem single_zero_swap (k i : Fin 7) :
    (Pi.single 0 (1 : FABL.𝔽₂) : FABL.F₂Cube 7) (Equiv.swap 0 k i) =
      (Pi.single k 1 : FABL.F₂Cube 7) i := by
  have h := Pi.single_comp_equiv (Equiv.swap 0 k) 0 (1 : FABL.𝔽₂)
  exact congrFun h i

private theorem exists_linearEquiv_single_zero_eq
    (u : FABL.F₂Cube 7) (hu : u ≠ 0) :
    ∃ L : FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7,
      L (Pi.single 0 1) = u := by
  have hexists : ∃ k, u k ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hexists
  have huk : u k = 1 := Fin.eq_one_of_ne_zero (u k) hk
  refine ⟨(swapZeroLinearEquiv k).trans (pivotShearLinearEquiv u k huk), ?_⟩
  ext i
  simp [swapZeroLinearEquiv, pivotShearLinearEquiv, single_zero_swap,
    add_left_comm, CharTwo.add_self_eq_zero]

private def quadraticPairingSevenKernel
    (f : BooleanFunction 7) (a b : FABL.F₂Cube 7) : FABL.𝔽₂ :=
  ∑ x, f x * FABL.f₂DotProductBilin 7 a x *
    FABL.f₂DotProductBilin 7 b x

private def quadraticPairingSeven (f : BooleanFunction 7) :
    LinearMap.BilinForm FABL.𝔽₂ (FABL.F₂Cube 7) :=
  LinearMap.mk₂ FABL.𝔽₂
    (quadraticPairingSevenKernel f)
    (by
      intro a₁ a₂ b
      simp only [quadraticPairingSevenKernel]
      simp_rw [map_add, LinearMap.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring)
    (by
      intro c a b
      simp only [quadraticPairingSevenKernel]
      simp_rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring)
    (by
      intro a b₁ b₂
      simp only [quadraticPairingSevenKernel]
      simp_rw [map_add, LinearMap.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring)
    (by
      intro c a b
      simp only [quadraticPairingSevenKernel]
      simp_rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring)

private theorem quadraticPairingSeven_apply
    (f : BooleanFunction 7) (a b : FABL.F₂Cube 7) :
    quadraticPairingSeven f a b = quadraticPairingSevenKernel f a b :=
  rfl

private theorem quadraticPairingSeven_isSymm (f : BooleanFunction 7) :
    (quadraticPairingSeven f).IsSymm := by
  constructor
  intro a b
  rw [quadraticPairingSeven_apply, quadraticPairingSeven_apply]
  simp only [quadraticPairingSevenKernel, FABL.f₂DotProductBilin_apply]
  apply Finset.sum_congr rfl
  intro x _
  ac_rfl

private theorem quadraticPairingSeven_isAlt_of_degree_le_five
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    (quadraticPairingSeven f).IsAlt := by
  intro a
  have hfdual : f ∈ reedMullerDual 1 7 := by
    rw [reedMullerDual_eq (r := 1) (n := 7) (by omega)]
    norm_num
    exact hf
  rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff] at hfdual
  have hpair := hfdual (FABL.affineFunction 0 a)
    (affineFunction_mem_reedMuller_one 0 a)
  rw [booleanFunctionPairing_apply] at hpair
  rw [quadraticPairingSeven_apply]
  simp only [quadraticPairingSevenKernel, FABL.f₂DotProductBilin_apply]
  calc
    (∑ x, f x * FABL.f₂DotProduct a x * FABL.f₂DotProduct a x) =
        ∑ x, FABL.affineFunction 0 a x * f x := by
      apply Finset.sum_congr rfl
      intro x _
      simp [FABL.affineFunction]
      by_cases hx : FABL.f₂DotProduct a x = 0
      · simp [hx]
      · have hxone : FABL.f₂DotProduct a x = 1 :=
          Fin.eq_one_of_ne_zero _ hx
        simp [hxone]
    _ = 0 := hpair

private theorem exists_nonzero_radical_quadraticPairingSeven
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    ∃ u : FABL.F₂Cube 7, u ≠ 0 ∧ ∀ v, quadraticPairingSeven f u v = 0 := by
  let B := quadraticPairingSeven f
  let A : Matrix (Fin 7) (Fin 7) FABL.𝔽₂ := B.toMatrix'
  have hAsymm : A.transpose = A := by
    exact ((LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm).mpr
      (quadraticPairingSeven_isSymm f)).eq
  have hAdiag : ∀ i, A i i = 0 := by
    intro i
    rw [show A i i = B (Pi.single i 1) (Pi.single i 1) by
      exact LinearMap.BilinForm.toMatrix'_apply B i i]
    exact quadraticPairingSeven_isAlt_of_degree_le_five f hf _
  obtain ⟨u, hu, hAu⟩ :=
    exists_nonzero_mulVec_eq_zero_of_symmetric_zero_diagonal_seven
      A hAsymm hAdiag
  refine ⟨u, hu, ?_⟩
  intro v
  have hvu : B v u = 0 := by
    calc
      B v u = Matrix.toBilin' A v u := by
        change B v u = Matrix.toBilin' B.toMatrix' v u
        rw [Matrix.toBilin'_toMatrix']
      _ = v ⬝ᵥ A.mulVec u := Matrix.toBilin'_apply' A v u
      _ = 0 := by rw [hAu, dotProduct_zero]
  exact (quadraticPairingSeven_isSymm f).eq v u |>.symm.trans hvu

private noncomputable def dotAdjointLinearEquiv
    (Q : FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7) :
    FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7 :=
  (dotProductEquiv FABL.𝔽₂ (Fin 7)).trans
    (Q.dualMap.trans (dotProductEquiv FABL.𝔽₂ (Fin 7)).symm)

private theorem f₂DotProduct_dotAdjointLinearEquiv
    (Q : FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7)
    (a x : FABL.F₂Cube 7) :
    FABL.f₂DotProduct (dotAdjointLinearEquiv Q a) x =
      FABL.f₂DotProduct a (Q x) := by
  change dotProduct (dotAdjointLinearEquiv Q a) x = dotProduct a (Q x)
  calc
    dotProduct (dotAdjointLinearEquiv Q a) x =
        (dotProductEquiv FABL.𝔽₂ (Fin 7)) (dotAdjointLinearEquiv Q a) x :=
      (dotProductEquiv_apply_apply FABL.𝔽₂ (Fin 7) _ _).symm
    _ = ((dotProductEquiv FABL.𝔽₂ (Fin 7)) a).comp Q.toLinearMap x := by
      exact DFunLike.congr_fun
        ((dotProductEquiv FABL.𝔽₂ (Fin 7)).apply_symm_apply
          (((dotProductEquiv FABL.𝔽₂ (Fin 7)) a).comp Q.toLinearMap)) x
    _ = dotProduct a (Q x) :=
      dotProductEquiv_apply_apply FABL.𝔽₂ (Fin 7) _ _

/-- The six-variable slice of a seven-variable Boolean function at a fixed
first coordinate. -/
def firstCoordinateSliceSeven
    (f : BooleanFunction 7) (c : FABL.𝔽₂) : BooleanFunction 6 :=
  fun y ↦ f (Fin.cons c y)

private def firstCoordinateFrequencyLiftSix
    (a : FABL.F₂Cube 6) : FABL.F₂Cube 7 :=
  Fin.cons 0 a

private theorem f₂DotProduct_firstCoordinateFrequencyLiftSix
    (a : FABL.F₂Cube 6) (x : FABL.F₂Cube 7) :
    FABL.f₂DotProduct (firstCoordinateFrequencyLiftSix a) x =
      FABL.f₂DotProduct a (Fin.tail x) := by
  change dotProduct (Fin.cons 0 a) x = dotProduct a (Fin.tail x)
  rw [dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
  rfl

private theorem f₂DotProduct_single_zero_seven
    (x : FABL.F₂Cube 7) :
    FABL.f₂DotProduct (Pi.single 0 1) x = x 0 := by
  simp [FABL.f₂DotProduct, dotProduct, Pi.single_apply]

private def firstCoordinateAffineExtension
    (c d : FABL.𝔽₂) (a : FABL.F₂Cube 6) : BooleanFunction 7 :=
  fun x ↦ if x 0 = c then FABL.affineFunction d a (Fin.tail x) else 0

private theorem firstCoordinateAffineExtension_decomposition
    (c d : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    firstCoordinateAffineExtension c d a =
      FABL.affineFunction ((1 + c) * d)
          ((1 + c) • firstCoordinateFrequencyLiftSix a +
            d • (Pi.single 0 1 : FABL.F₂Cube 7)) +
        fun x ↦
          FABL.f₂DotProduct (Pi.single 0 1) x *
            FABL.f₂DotProduct (firstCoordinateFrequencyLiftSix a) x := by
  funext x
  simp only [Pi.add_apply]
  rw [f₂DotProduct_firstCoordinateFrequencyLiftSix,
    f₂DotProduct_single_zero_seven]
  simp only [firstCoordinateAffineExtension, FABL.affineFunction]
  have hdot :
      FABL.f₂DotProduct
          ((1 + c) • firstCoordinateFrequencyLiftSix a +
            d • (Pi.single 0 1 : FABL.F₂Cube 7)) x =
        (1 + c) * FABL.f₂DotProduct (firstCoordinateFrequencyLiftSix a) x +
          d * FABL.f₂DotProduct (Pi.single 0 1) x := by
    simp only [FABL.f₂DotProduct, add_dotProduct, smul_dotProduct,
      smul_eq_mul]
  rw [hdot]
  rw [f₂DotProduct_firstCoordinateFrequencyLiftSix,
    f₂DotProduct_single_zero_seven]
  generalize x 0 = x₀
  generalize FABL.f₂DotProduct a (Fin.tail x) = z
  fin_cases c <;> fin_cases d <;> fin_cases x₀ <;> fin_cases z <;> decide

private theorem booleanFunctionPairing_firstCoordinateAffineExtension
    (f : BooleanFunction 7) (c d : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    booleanFunctionPairing 7 f (firstCoordinateAffineExtension c d a) =
      booleanFunctionPairing 6 (firstCoordinateSliceSeven f c)
        (FABL.affineFunction d a) := by
  classical
  rw [booleanFunctionPairing_apply, booleanFunctionPairing_apply]
  rw [← Equiv.sum_comp (Fin.consEquiv
    (fun _ : Fin 7 ↦ FABL.𝔽₂)), Fintype.sum_prod_type]
  change (∑ c' : FABL.𝔽₂, ∑ y : FABL.F₂Cube 6,
    f (Fin.cons c' y) * firstCoordinateAffineExtension c d a (Fin.cons c' y)) = _
  fin_cases c <;>
    simp [firstCoordinateAffineExtension, firstCoordinateSliceSeven]

private theorem firstCoordinateSliceSeven_degree_le_four_of_radical
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (hradical : ∀ a, quadraticPairingSeven f (Pi.single 0 1) a = 0)
    (c : FABL.𝔽₂) :
    FABL.functionAlgebraicDegree (firstCoordinateSliceSeven f c) ≤ 4 := by
  have hfdual : f ∈ reedMullerDual 1 7 := by
    rw [reedMullerDual_eq (r := 1) (n := 7) (by omega)]
    norm_num
    exact hf
  rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff] at hfdual
  have hsliceDual : firstCoordinateSliceSeven f c ∈ reedMullerDual 1 6 := by
    rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff]
    intro q hq
    rw [mem_reedMuller_iff] at hq
    obtain ⟨d, a, rfl⟩ :=
      FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one q hq
    have hpairingComm :
        booleanFunctionPairing 6 (FABL.affineFunction d a)
            (firstCoordinateSliceSeven f c) =
          booleanFunctionPairing 6 (firstCoordinateSliceSeven f c)
            (FABL.affineFunction d a) := by
      rw [booleanFunctionPairing_apply, booleanFunctionPairing_apply]
      apply Finset.sum_congr rfl
      intro x _
      exact mul_comm _ _
    rw [hpairingComm]
    rw [← booleanFunctionPairing_firstCoordinateAffineExtension]
    rw [firstCoordinateAffineExtension_decomposition]
    rw [map_add]
    have haffine := hfdual
      (FABL.affineFunction ((1 + c) * d)
        ((1 + c) • firstCoordinateFrequencyLiftSix a +
          d • (Pi.single 0 1 : FABL.F₂Cube 7)))
      (affineFunction_mem_reedMuller_one _ _)
    have haffine' :
        booleanFunctionPairing 7 f
            (FABL.affineFunction ((1 + c) * d)
              ((1 + c) • firstCoordinateFrequencyLiftSix a +
                d • (Pi.single 0 1 : FABL.F₂Cube 7))) = 0 := by
      calc
        booleanFunctionPairing 7 f
            (FABL.affineFunction ((1 + c) * d)
              ((1 + c) • firstCoordinateFrequencyLiftSix a +
                d • (Pi.single 0 1 : FABL.F₂Cube 7))) =
            booleanFunctionPairing 7
              (FABL.affineFunction ((1 + c) * d)
                ((1 + c) • firstCoordinateFrequencyLiftSix a +
                  d • (Pi.single 0 1 : FABL.F₂Cube 7))) f := by
              rw [booleanFunctionPairing_apply, booleanFunctionPairing_apply]
              apply Finset.sum_congr rfl
              intro x _
              exact mul_comm _ _
        _ = 0 := haffine
    rw [haffine', zero_add]
    rw [booleanFunctionPairing_apply]
    have hrad := hradical (firstCoordinateFrequencyLiftSix a)
    rw [quadraticPairingSeven_apply] at hrad
    simp only [quadraticPairingSevenKernel, FABL.f₂DotProductBilin_apply] at hrad
    calc
      (∑ x, f x * (FABL.f₂DotProduct (Pi.single 0 1) x *
          FABL.f₂DotProduct (firstCoordinateFrequencyLiftSix a) x)) =
          ∑ x, f x * FABL.f₂DotProduct (Pi.single 0 1) x *
            FABL.f₂DotProduct (firstCoordinateFrequencyLiftSix a) x := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := hrad
  rw [reedMullerDual_eq (r := 1) (n := 6) (by omega)] at hsliceDual
  norm_num at hsliceDual
  exact hsliceDual

private theorem f₂DotProduct_map_dotAdjoint_symm
    (Q : FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7)
    (a y : FABL.F₂Cube 7) :
    FABL.f₂DotProduct (Q a) (dotAdjointLinearEquiv Q.symm y) =
      FABL.f₂DotProduct a y := by
  calc
    FABL.f₂DotProduct (Q a) (dotAdjointLinearEquiv Q.symm y) =
        FABL.f₂DotProduct (dotAdjointLinearEquiv Q.symm y) (Q a) :=
      dotProduct_comm _ _
    _ = FABL.f₂DotProduct y (Q.symm (Q a)) :=
      f₂DotProduct_dotAdjointLinearEquiv Q.symm y (Q a)
    _ = FABL.f₂DotProduct y a := by rw [Q.symm_apply_apply]
    _ = FABL.f₂DotProduct a y := dotProduct_comm _ _

private theorem quadraticPairingSeven_comp_dotAdjoint_symm
    (f : BooleanFunction 7)
    (Q : FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7)
    (a b : FABL.F₂Cube 7) :
    quadraticPairingSeven (f ∘ dotAdjointLinearEquiv Q.symm) a b =
      quadraticPairingSeven f (Q a) (Q b) := by
  classical
  rw [quadraticPairingSeven_apply, quadraticPairingSeven_apply]
  simp only [quadraticPairingSevenKernel, FABL.f₂DotProductBilin_apply]
  apply Fintype.sum_equiv (dotAdjointLinearEquiv Q.symm).toEquiv
  intro y
  simp only [Function.comp_apply]
  change f (dotAdjointLinearEquiv Q.symm y) *
      FABL.f₂DotProduct a y * FABL.f₂DotProduct b y =
    f (dotAdjointLinearEquiv Q.symm y) *
      FABL.f₂DotProduct (Q a) (dotAdjointLinearEquiv Q.symm y) *
        FABL.f₂DotProduct (Q b) (dotAdjointLinearEquiv Q.symm y)
  rw [f₂DotProduct_map_dotAdjoint_symm,
    f₂DotProduct_map_dotAdjoint_symm]

/-- Hou's odd-dimensional degree-five normal form: after an invertible
linear change of variables, both six-variable coordinate slices have degree
at most four. -/
theorem exists_linearEquiv_firstCoordinateSlices_degree_le_four
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    ∃ P : FABL.F₂Cube 7 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 7,
      FABL.functionAlgebraicDegree
          (firstCoordinateSliceSeven (f ∘ P) 0) ≤ 4 ∧
        FABL.functionAlgebraicDegree
          (firstCoordinateSliceSeven (f ∘ P) 1) ≤ 4 := by
  obtain ⟨u, hu, huradical⟩ :=
    exists_nonzero_radical_quadraticPairingSeven f hf
  obtain ⟨Q, hQ⟩ := exists_linearEquiv_single_zero_eq u hu
  let P := dotAdjointLinearEquiv Q.symm
  have hdegree : FABL.functionAlgebraicDegree (f ∘ P) ≤ 5 := by
    have hcomp : (f ∘ P : BooleanFunction 7) = f ∘ P.toAffineEquiv := rfl
    rw [hcomp, FABL.functionAlgebraicDegree_comp_affineEquiv]
    exact hf
  have hradical : ∀ a,
      quadraticPairingSeven (f ∘ P) (Pi.single 0 1) a = 0 := by
    intro a
    rw [show quadraticPairingSeven (f ∘ P) (Pi.single 0 1) a =
        quadraticPairingSeven f (Q (Pi.single 0 1)) (Q a) by
      exact quadraticPairingSeven_comp_dotAdjoint_symm f Q _ _]
    rw [hQ]
    exact huradical (Q a)
  exact ⟨P,
    firstCoordinateSliceSeven_degree_le_four_of_radical
      (f ∘ P) hdegree hradical 0,
    firstCoordinateSliceSeven_degree_le_four_of_radical
      (f ∘ P) hdegree hradical 1⟩


private theorem nonlinearity_le_affineFunction_distance
    (f : BooleanFunction n) (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    nonlinearity f ≤ hammingDistance f (FABL.affineFunction b a) := by
  unfold nonlinearity
  exact Finset.inf'_le _ (Finset.mem_univ (b, a))

private theorem nonlinearity_six_le_twenty_eight
    (f : BooleanFunction 6) : nonlinearity f ≤ 28 := by
  have hbound := nonlinearity_cast_le_coveringRadius f
  have hvalue :
      (2 : ℝ) ^ (6 : ℕ) / 2 - Real.sqrt ((2 : ℝ) ^ (6 : ℕ)) / 2 = 28 := by
    norm_num
  rw [hvalue] at hbound
  exact_mod_cast hbound

private theorem nonlinearity_seven_le_fifty_eight
    (f : BooleanFunction 7) : nonlinearity f ≤ 58 := by
  have hbound := nonlinearity_cast_le_coveringRadius f
  have hpow : (2 : ℝ) ^ (7 : ℕ) = 128 := by norm_num
  rw [hpow] at hbound
  have hsqrt : (10 : ℝ) < Real.sqrt 128 := by
    calc
      (10 : ℝ) = Real.sqrt 100 := by norm_num
      _ < Real.sqrt 128 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlt : (nonlinearity f : ℝ) < 59 := by linarith
  have hnat : nonlinearity f < 59 := by exact_mod_cast hlt
  omega

private theorem exists_affineFunction_same_slope_distance_le_thirty_two
    (f : BooleanFunction 6) (a : FABL.F₂Cube 6) :
    ∃ b, hammingDistance f (FABL.affineFunction b a) ≤ 32 := by
  by_cases hwalsh : 0 ≤ walshTransform f a
  · refine ⟨0, ?_⟩
    have hdistance := hammingDistance_cast_linearFunction_eq f a
    norm_num at hdistance
    have hwalshReal : 0 ≤ (walshTransform f a : ℝ) := by
      exact_mod_cast hwalsh
    have hcast :
        (hammingDistance f (FABL.affineFunction 0 a) : ℝ) ≤ 32 := by
      linarith
    exact_mod_cast hcast
  · refine ⟨1, ?_⟩
    have hdistance := hammingDistance_cast_complementLinearFunction_eq f a
    norm_num at hdistance
    have hwalshReal : (walshTransform f a : ℝ) < 0 := by
      exact_mod_cast (lt_of_not_ge hwalsh)
    have hcast :
        (hammingDistance f (FABL.affineFunction 1 a) : ℝ) ≤ 32 := by
      linarith
    exact_mod_cast hcast

private theorem exists_affineFunction_same_slope_distance_eq_twenty_eight
    (f : BooleanFunction 6) (hf : nonlinearity f = 28)
    (a : FABL.F₂Cube 6) :
    ∃ b, hammingDistance f (FABL.affineFunction b a) = 28 := by
  have habs := natAbs_walshTransform_eq_eight_of_nonlinearity_eq_28 f hf a
  rcases Int.natAbs_eq (walshTransform f a) with hwalsh | hwalsh <;>
    rw [habs] at hwalsh
  · refine ⟨0, ?_⟩
    have hdistance := hammingDistance_cast_linearFunction_eq f a
    rw [hwalsh] at hdistance
    norm_num at hdistance
    exact_mod_cast hdistance
  · refine ⟨1, ?_⟩
    have hdistance := hammingDistance_cast_complementLinearFunction_eq f a
    rw [hwalsh] at hdistance
    norm_num at hdistance
    exact_mod_cast hdistance

private def pairedAffineFunctionSeven
    (bzero bone : FABL.𝔽₂) (a : FABL.F₂Cube 6) : BooleanFunction 7 :=
  FABL.affineFunction bzero (Fin.cons (bzero + bone) a)

private theorem firstCoordinateSliceSeven_pairedAffineFunction_zero
    (bzero bone : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    firstCoordinateSliceSeven (pairedAffineFunctionSeven bzero bone a) 0 =
      FABL.affineFunction bzero a := by
  funext x
  simp [firstCoordinateSliceSeven, pairedAffineFunctionSeven,
    FABL.affineFunction, FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ]

private theorem firstCoordinateSliceSeven_pairedAffineFunction_one
    (bzero bone : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    firstCoordinateSliceSeven (pairedAffineFunctionSeven bzero bone a) 1 =
      FABL.affineFunction bone a := by
  funext x
  simp only [firstCoordinateSliceSeven, pairedAffineFunctionSeven,
    FABL.affineFunction]
  have hdot :
      FABL.f₂DotProduct (Fin.cons (bzero + bone) a) (Fin.cons 1 x) =
        (bzero + bone) * 1 + FABL.f₂DotProduct a x := by
    exact Matrix.cons_dotProduct_cons (bzero + bone) a 1 x
  rw [hdot]
  simp only [mul_one]
  rw [add_assoc bzero bone, ← add_assoc bzero bzero,
    CharTwo.add_self_eq_zero, zero_add]

private theorem hammingDistance_firstCoordinateSlicesSeven
    (f g : BooleanFunction 7) :
    hammingDistance f g =
      hammingDistance (firstCoordinateSliceSeven f 0)
          (firstCoordinateSliceSeven g 0) +
        hammingDistance (firstCoordinateSliceSeven f 1)
          (firstCoordinateSliceSeven g 1) := by
  classical
  unfold hammingDistance hammingDist
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  change (∑ x : FABL.F₂Cube 7, if f x ≠ g x then 1 else 0) = _
  rw [← Equiv.sum_comp (Fin.consEquiv
    (fun _ : Fin 7 ↦ FABL.𝔽₂)), Fintype.sum_prod_type]
  change (∑ b : FABL.𝔽₂, ∑ x : FABL.F₂Cube 6,
    if f (Fin.cons b x) ≠ g (Fin.cons b x) then 1 else 0) = _
  rw [show (Finset.univ : Finset FABL.𝔽₂) = {0, 1} by rfl]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton]
  rfl

private theorem hammingDistance_pairedAffineFunctionSeven
    (f : BooleanFunction 7) (bzero bone : FABL.𝔽₂)
    (a : FABL.F₂Cube 6) :
    hammingDistance f (pairedAffineFunctionSeven bzero bone a) =
      hammingDistance (firstCoordinateSliceSeven f 0)
          (FABL.affineFunction bzero a) +
        hammingDistance (firstCoordinateSliceSeven f 1)
          (FABL.affineFunction bone a) := by
  rw [hammingDistance_firstCoordinateSlicesSeven,
    firstCoordinateSliceSeven_pairedAffineFunction_zero,
    firstCoordinateSliceSeven_pairedAffineFunction_one]

private theorem firstCoordinateSliceSeven_affineFunction_zero
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 7) :
    firstCoordinateSliceSeven (FABL.affineFunction b a) 0 =
      FABL.affineFunction b (Fin.tail a) := by
  funext x
  simp only [firstCoordinateSliceSeven, FABL.affineFunction]
  have hdot : FABL.f₂DotProduct a (Fin.cons 0 x) =
      a 0 * 0 + FABL.f₂DotProduct (Fin.tail a) x := by
    exact Matrix.dotProduct_cons a 0 x
  rw [hdot]
  simp

private theorem firstCoordinateSliceSeven_affineFunction_one
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 7) :
    firstCoordinateSliceSeven (FABL.affineFunction b a) 1 =
      FABL.affineFunction (b + a 0) (Fin.tail a) := by
  funext x
  simp only [firstCoordinateSliceSeven, FABL.affineFunction]
  have hdot : FABL.f₂DotProduct a (Fin.cons 1 x) =
      a 0 * 1 + FABL.f₂DotProduct (Fin.tail a) x := by
    exact Matrix.dotProduct_cons a 1 x
  rw [hdot]
  simp only [Fin.isValue, mul_one, Nat.reduceAdd]
  rw [add_assoc]

private theorem slice_nonlinearity_sum_le_nonlinearity_seven
    (f : BooleanFunction 7) :
    nonlinearity (firstCoordinateSliceSeven f 0) +
        nonlinearity (firstCoordinateSliceSeven f 1) ≤ nonlinearity f := by
  obtain ⟨b, a, haffine⟩ :=
    exists_affineFunction_hammingDistance_eq_nonlinearity f
  have hzero := nonlinearity_le_affineFunction_distance
    (firstCoordinateSliceSeven f 0) b (Fin.tail a)
  have hone := nonlinearity_le_affineFunction_distance
    (firstCoordinateSliceSeven f 1) (b + a 0) (Fin.tail a)
  calc
    nonlinearity (firstCoordinateSliceSeven f 0) +
        nonlinearity (firstCoordinateSliceSeven f 1) ≤
        hammingDistance (firstCoordinateSliceSeven f 0)
            (FABL.affineFunction b (Fin.tail a)) +
          hammingDistance (firstCoordinateSliceSeven f 1)
            (FABL.affineFunction (b + a 0) (Fin.tail a)) :=
      Nat.add_le_add hzero hone
    _ = hammingDistance f (FABL.affineFunction b a) := by
      rw [hammingDistance_firstCoordinateSlicesSeven]
      rw [firstCoordinateSliceSeven_affineFunction_zero,
        firstCoordinateSliceSeven_affineFunction_one]
    _ = nonlinearity f := haffine

private theorem nonlinearity_seven_le_slice_affine_distances
    (f : BooleanFunction 7) (bzero bone : FABL.𝔽₂)
    (a : FABL.F₂Cube 6) :
    nonlinearity f ≤
      hammingDistance (firstCoordinateSliceSeven f 0)
          (FABL.affineFunction bzero a) +
        hammingDistance (firstCoordinateSliceSeven f 1)
          (FABL.affineFunction bone a) := by
  calc
    nonlinearity f ≤
        hammingDistance f (pairedAffineFunctionSeven bzero bone a) :=
      nonlinearity_le_affineFunction_distance f bzero
        (Fin.cons (bzero + bone) a)
    _ = _ := hammingDistance_pairedAffineFunctionSeven f bzero bone a

private theorem nonlinearity_seven_eq_twenty_eight_add_slice_one
    (f : BooleanFunction 7)
    (hzero : nonlinearity (firstCoordinateSliceSeven f 0) = 28) :
    nonlinearity f = 28 + nonlinearity (firstCoordinateSliceSeven f 1) := by
  apply Nat.le_antisymm
  · obtain ⟨bone, a, hone⟩ :=
      exists_affineFunction_hammingDistance_eq_nonlinearity
        (firstCoordinateSliceSeven f 1)
    obtain ⟨bzero, hzeroDistance⟩ :=
      exists_affineFunction_same_slope_distance_eq_twenty_eight
        (firstCoordinateSliceSeven f 0) hzero a
    calc
      nonlinearity f ≤
          hammingDistance (firstCoordinateSliceSeven f 0)
              (FABL.affineFunction bzero a) +
            hammingDistance (firstCoordinateSliceSeven f 1)
              (FABL.affineFunction bone a) :=
        nonlinearity_seven_le_slice_affine_distances f bzero bone a
      _ = 28 + nonlinearity (firstCoordinateSliceSeven f 1) := by
        rw [hzeroDistance, hone]
  · rw [← hzero]
    exact slice_nonlinearity_sum_le_nonlinearity_seven f

private theorem nonlinearity_seven_eq_slice_zero_add_twenty_eight
    (f : BooleanFunction 7)
    (hone : nonlinearity (firstCoordinateSliceSeven f 1) = 28) :
    nonlinearity f = nonlinearity (firstCoordinateSliceSeven f 0) + 28 := by
  apply Nat.le_antisymm
  · obtain ⟨bzero, a, hzero⟩ :=
      exists_affineFunction_hammingDistance_eq_nonlinearity
        (firstCoordinateSliceSeven f 0)
    obtain ⟨bone, honeDistance⟩ :=
      exists_affineFunction_same_slope_distance_eq_twenty_eight
        (firstCoordinateSliceSeven f 1) hone a
    calc
      nonlinearity f ≤
          hammingDistance (firstCoordinateSliceSeven f 0)
              (FABL.affineFunction bzero a) +
            hammingDistance (firstCoordinateSliceSeven f 1)
              (FABL.affineFunction bone a) :=
        nonlinearity_seven_le_slice_affine_distances f bzero bone a
      _ = nonlinearity (firstCoordinateSliceSeven f 0) + 28 := by
        rw [hzero, honeDistance]
  · rw [← hone]
    exact slice_nonlinearity_sum_le_nonlinearity_seven f

private theorem four_dvd_hammingWeight_affineFunction_seven
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 7) :
    4 ∣ hammingWeight (FABL.affineFunction b a) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      have hzero :
          FABL.affineFunction (0 : FABL.𝔽₂) (0 : FABL.F₂Cube 7) = 0 := by
        funext x
        simp [FABL.affineFunction, FABL.f₂DotProduct]
      rw [hzero]
      simp
    · have hb_one : b = 1 := Fin.eq_one_of_ne_zero _ hb
      subst b
      rw [hammingWeight_affineFunction_one_zero]
      norm_num
  · rw [hammingWeight_affineFunction_of_ne_zero b a ha]
    norm_num

private theorem even_support_inter_affineFunction_of_degree_le_five
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 7) :
    Even (support f ∩ support (FABL.affineFunction b a)).card := by
  have hfmem : f ∈ reedMuller 5 7 := hf
  have hfdual : f ∈ reedMullerDual 1 7 := by
    rw [reedMullerDual_eq (r := 1) (n := 7) (by omega)]
    norm_num
    exact hfmem
  rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff] at hfdual
  have hpair := hfdual (FABL.affineFunction b a)
    (affineFunction_mem_reedMuller_one b a)
  exact even_card_support_inter_of_pairing_eq_zero f
    (FABL.affineFunction b a) (by
      rw [booleanFunctionPairing_apply]
      calc
        ∑ x, f x * FABL.affineFunction b a x =
            ∑ x, FABL.affineFunction b a x * f x := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact mul_comm _ _
        _ = 0 := hpair)

private theorem hammingDistance_affineFunction_mod_four_eq_weight_mod_four_seven
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 7) :
    hammingDistance f (FABL.affineFunction b a) % 4 = hammingWeight f % 4 := by
  rw [hammingDistance_eq_hammingWeight_add]
  have hidentity := hammingWeight_add_add_two_mul_card_inter f
    (FABL.affineFunction b a)
  obtain ⟨k, hk⟩ :=
    even_support_inter_affineFunction_of_degree_le_five f hf b a
  obtain ⟨q, hq⟩ := four_dvd_hammingWeight_affineFunction_seven b a
  omega

private theorem even_hammingWeight_of_degree_le_four_six
    (f : BooleanFunction 6) (hf : FABL.functionAlgebraicDegree f ≤ 4) :
    Even (hammingWeight f) := by
  have heven := even_support_inter_affineFunction_of_degree_le_four
    f hf 1 0
  have hone :
      FABL.affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube 6) = 1 := by
    funext x
    simp [FABL.affineFunction, FABL.f₂DotProduct]
  rw [hone] at heven
  simpa [hammingWeight_eq_card_support, support, FABL.f₂OneSupport] using heven

private theorem even_hammingWeight_of_degree_le_five_seven
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    Even (hammingWeight f) := by
  have heven := even_support_inter_affineFunction_of_degree_le_five
    f hf 1 0
  have hone :
      FABL.affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube 7) = 1 := by
    funext x
    simp [FABL.affineFunction, FABL.f₂DotProduct]
  rw [hone] at heven
  simpa [hammingWeight_eq_card_support, support, FABL.f₂OneSupport] using heven

private theorem even_nonlinearity_of_degree_le_four_six
    (f : BooleanFunction 6) (hf : FABL.functionAlgebraicDegree f ≤ 4) :
    Even (nonlinearity f) := by
  obtain ⟨b, a, hminimum⟩ :=
    exists_affineFunction_hammingDistance_eq_nonlinearity f
  have hmod := hammingDistance_affineFunction_mod_four_eq_weight_mod_four
    f hf b a
  obtain ⟨k, hk⟩ := even_hammingWeight_of_degree_le_four_six f hf
  rw [hminimum, hk] at hmod
  exact ⟨nonlinearity f / 2, by omega⟩

private theorem even_nonlinearity_of_degree_le_five_seven
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    Even (nonlinearity f) := by
  obtain ⟨b, a, hminimum⟩ :=
    exists_affineFunction_hammingDistance_eq_nonlinearity f
  have hmod :=
    hammingDistance_affineFunction_mod_four_eq_weight_mod_four_seven
      f hf b a
  obtain ⟨k, hk⟩ := even_hammingWeight_of_degree_le_five_seven f hf
  rw [hminimum, hk] at hmod
  exact ⟨nonlinearity f / 2, by omega⟩

private theorem hammingDistance_affineFunction_add_one_sum_six
    (f : BooleanFunction 6) (b : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    hammingDistance f (FABL.affineFunction b a) +
        hammingDistance f (FABL.affineFunction (b + 1) a) = 64 := by
  by_cases hb : b = 0
  · subst b
    change hammingDistance f (FABL.affineFunction 0 a) +
        hammingDistance f (FABL.affineFunction 1 a) = 64
    apply (Nat.cast_injective : Function.Injective (fun k : ℕ ↦ (k : ℝ)))
    push_cast
    have hzero := hammingDistance_cast_linearFunction_eq f a
    have hone := hammingDistance_cast_complementLinearFunction_eq f a
    norm_num at hzero hone
    linarith
  · have hb_one : b = 1 := Fin.eq_one_of_ne_zero _ hb
    subst b
    change hammingDistance f (FABL.affineFunction 1 a) +
        hammingDistance f (FABL.affineFunction 0 a) = 64
    apply (Nat.cast_injective : Function.Injective (fun k : ℕ ↦ (k : ℝ)))
    push_cast
    have hone := hammingDistance_cast_complementLinearFunction_eq f a
    have hzero := hammingDistance_cast_linearFunction_eq f a
    norm_num at hzero hone
    linarith

private theorem nonlinearity_le_fifty_six_of_slices_degree_le_four
    (f : BooleanFunction 7)
    (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (hzeroDegree :
      FABL.functionAlgebraicDegree (firstCoordinateSliceSeven f 0) ≤ 4)
    (honeDegree :
      FABL.functionAlgebraicDegree (firstCoordinateSliceSeven f 1) ≤ 4) :
    nonlinearity f ≤ 56 := by
  by_contra hbound
  have hgreater : 56 < nonlinearity f := Nat.lt_of_not_ge hbound
  have hupper := nonlinearity_seven_le_fifty_eight f
  obtain ⟨k, hk⟩ := even_nonlinearity_of_degree_le_five_seven f hf
  have hnonlinearity : nonlinearity f = 58 := by omega
  have hzeroUpper :=
    nonlinearity_six_le_twenty_eight (firstCoordinateSliceSeven f 0)
  obtain ⟨j, hj⟩ := even_nonlinearity_of_degree_le_four_six
    (firstCoordinateSliceSeven f 0) hzeroDegree
  have hzeroCases :
      nonlinearity (firstCoordinateSliceSeven f 0) = 28 ∨
        nonlinearity (firstCoordinateSliceSeven f 0) = 26 ∨
          nonlinearity (firstCoordinateSliceSeven f 0) ≤ 24 := by
    omega
  rcases hzeroCases with hzero | hzero | hzero
  · have hequality :=
      nonlinearity_seven_eq_twenty_eight_add_slice_one f hzero
    have honeUpper :=
      nonlinearity_six_le_twenty_eight (firstCoordinateSliceSeven f 1)
    omega
  · obtain ⟨bzero, a, hzeroDistance⟩ :=
      exists_affineFunction_hammingDistance_eq_nonlinearity
        (firstCoordinateSliceSeven f 0)
    rw [hzero] at hzeroDistance
    obtain ⟨bone, honeDistance⟩ :=
      exists_affineFunction_same_slope_distance_le_thirty_two
        (firstCoordinateSliceSeven f 1) a
    have hcandidate :=
      nonlinearity_seven_le_slice_affine_distances f bzero bone a
    rw [hnonlinearity, hzeroDistance] at hcandidate
    have honeDistanceEq :
        hammingDistance (firstCoordinateSliceSeven f 1)
          (FABL.affineFunction bone a) = 32 := by
      omega
    have honeDistanceMod :=
      hammingDistance_affineFunction_mod_four_eq_weight_mod_four
        (firstCoordinateSliceSeven f 1) honeDegree bone a
    obtain ⟨boneMin, aMin, honeMin⟩ :=
      exists_affineFunction_hammingDistance_eq_nonlinearity
        (firstCoordinateSliceSeven f 1)
    have honeMinMod :=
      hammingDistance_affineFunction_mod_four_eq_weight_mod_four
        (firstCoordinateSliceSeven f 1) honeDegree boneMin aMin
    rw [honeDistanceEq] at honeDistanceMod
    rw [honeMin] at honeMinMod
    have honeMod : nonlinearity (firstCoordinateSliceSeven f 1) % 4 = 0 := by
      omega
    have honeUpper :=
      nonlinearity_six_le_twenty_eight (firstCoordinateSliceSeven f 1)
    by_cases hone : nonlinearity (firstCoordinateSliceSeven f 1) = 28
    · have hequality :=
        nonlinearity_seven_eq_slice_zero_add_twenty_eight f hone
      omega
    · have honeLe : nonlinearity (firstCoordinateSliceSeven f 1) ≤ 24 := by
        omega
      obtain ⟨boneMin, aMin, honeMin⟩ :=
        exists_affineFunction_hammingDistance_eq_nonlinearity
          (firstCoordinateSliceSeven f 1)
      obtain ⟨bzeroNear, hzeroNear⟩ :=
        exists_affineFunction_same_slope_distance_le_thirty_two
          (firstCoordinateSliceSeven f 0) aMin
      have hcandidate' :=
        nonlinearity_seven_le_slice_affine_distances
          f bzeroNear boneMin aMin
      rw [honeMin] at hcandidate'
      omega
  · obtain ⟨bzero, a, hzeroDistance⟩ :=
      exists_affineFunction_hammingDistance_eq_nonlinearity
        (firstCoordinateSliceSeven f 0)
    obtain ⟨bone, honeDistance⟩ :=
      exists_affineFunction_same_slope_distance_le_thirty_two
        (firstCoordinateSliceSeven f 1) a
    have hcandidate :=
      nonlinearity_seven_le_slice_affine_distances f bzero bone a
    rw [hzeroDistance] at hcandidate
    omega

/-- Every seven-variable Boolean function of algebraic degree at most five
has nonlinearity at most `56`. -/
theorem nonlinearity_le_56_of_degree_le_five_seven
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    nonlinearity f ≤ 56 := by
  obtain ⟨P, hzero, hone⟩ :=
    exists_linearEquiv_firstCoordinateSlices_degree_le_four f hf
  let g : BooleanFunction 7 := f ∘ P
  have hgDegree : FABL.functionAlgebraicDegree g ≤ 5 := by
    have hcomp : g = f ∘ P.toAffineEquiv := rfl
    rw [hcomp, FABL.functionAlgebraicDegree_comp_affineEquiv]
    exact hf
  have hg := nonlinearity_le_fifty_six_of_slices_degree_le_four
    g hgDegree (by simpa [g] using hzero) (by simpa [g] using hone)
  have hinvariant := nonlinearity_comp_affineEquiv f P.toAffineEquiv
  change nonlinearity g = nonlinearity f at hinvariant
  rwa [hinvariant] at hg

private theorem hammingDistance_affineFunction_mod_four_eq_nonlinearity_mod_four_six
    (f : BooleanFunction 6) (hf : FABL.functionAlgebraicDegree f ≤ 4)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 6) :
    hammingDistance f (FABL.affineFunction b a) % 4 = nonlinearity f % 4 := by
  obtain ⟨bmin, amin, hminimum⟩ :=
    exists_affineFunction_hammingDistance_eq_nonlinearity f
  have hcandidate := hammingDistance_affineFunction_mod_four_eq_weight_mod_four
    f hf b a
  have hminimumMod := hammingDistance_affineFunction_mod_four_eq_weight_mod_four
    f hf bmin amin
  rw [hminimum] at hminimumMod
  omega

private theorem hammingDistance_affineFunction_mod_four_eq_nonlinearity_mod_four_seven
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube 7) :
    hammingDistance f (FABL.affineFunction b a) % 4 = nonlinearity f % 4 := by
  obtain ⟨bmin, amin, hminimum⟩ :=
    exists_affineFunction_hammingDistance_eq_nonlinearity f
  have hcandidate :=
    hammingDistance_affineFunction_mod_four_eq_weight_mod_four_seven
      f hf b a
  have hminimumMod :=
    hammingDistance_affineFunction_mod_four_eq_weight_mod_four_seven
      f hf bmin amin
  rw [hminimum] at hminimumMod
  omega

private theorem pairedAffineFunctionSeven_error_zero_slice
    (f : BooleanFunction 7) (bzero bone : FABL.𝔽₂)
    (a : FABL.F₂Cube 6) (x : FABL.F₂Cube 6) :
    (f + pairedAffineFunctionSeven bzero bone a) (Fin.cons 0 x) =
      (firstCoordinateSliceSeven f 0 + FABL.affineFunction bzero a) x := by
  simp only [Pi.add_apply, firstCoordinateSliceSeven]
  rw [show pairedAffineFunctionSeven bzero bone a (Fin.cons 0 x) =
      FABL.affineFunction bzero a x by
    exact congrFun
      (firstCoordinateSliceSeven_pairedAffineFunction_zero bzero bone a) x]

private theorem exists_minimum_pairedAffineFunction_error_one_at_zero_slice
    (f : BooleanFunction 7)
    (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (hzeroDegree :
      FABL.functionAlgebraicDegree (firstCoordinateSliceSeven f 0) ≤ 4)
    (honeDegree :
      FABL.functionAlgebraicDegree (firstCoordinateSliceSeven f 1) ≤ 4)
    (hnonlinearity : nonlinearity f = 56)
    (x : FABL.F₂Cube 6) :
    ∃ bzero bone a,
      hammingDistance f (pairedAffineFunctionSeven bzero bone a) = 56 ∧
        (f + pairedAffineFunctionSeven bzero bone a) (Fin.cons 0 x) = 1 := by
  have hzeroUpper :=
    nonlinearity_six_le_twenty_eight (firstCoordinateSliceSeven f 0)
  obtain ⟨k, hk⟩ := even_nonlinearity_of_degree_le_four_six
    (firstCoordinateSliceSeven f 0) hzeroDegree
  have hzeroCases :
      nonlinearity (firstCoordinateSliceSeven f 0) = 28 ∨
        nonlinearity (firstCoordinateSliceSeven f 0) = 26 ∨
          nonlinearity (firstCoordinateSliceSeven f 0) ≤ 24 := by
    omega
  rcases hzeroCases with hzero | hzero | hzero
  · have hequality :=
      nonlinearity_seven_eq_twenty_eight_add_slice_one f hzero
    have hone : nonlinearity (firstCoordinateSliceSeven f 1) = 28 := by
      omega
    obtain ⟨bzero, a, hzeroDistance, hzeroPoint⟩ :=
      exists_minimum_affine_error_one_at_of_nonlinearity_eq_28
        (firstCoordinateSliceSeven f 0) hzero x
    obtain ⟨bone, honeDistance⟩ :=
      exists_affineFunction_same_slope_distance_eq_twenty_eight
        (firstCoordinateSliceSeven f 1) hone a
    refine ⟨bzero, bone, a, ?_, ?_⟩
    · rw [hammingDistance_pairedAffineFunctionSeven,
        hzeroDistance, honeDistance]
    · rw [pairedAffineFunctionSeven_error_zero_slice]
      exact hzeroPoint
  · obtain ⟨bzero, a, hzeroDistance, hzeroPoint⟩ :=
      exists_minimum_affine_error_one_at_of_degree_le_four_nonlinearity_eq_26
        (firstCoordinateSliceSeven f 0) hzeroDegree hzero x
    obtain ⟨bone, honeDistance⟩ :=
      exists_affineFunction_same_slope_distance_le_thirty_two
        (firstCoordinateSliceSeven f 1) a
    have hcandidateLower :=
      nonlinearity_le_affineFunction_distance f bzero
        (Fin.cons (bzero + bone) a)
    have hcandidateMod :=
      hammingDistance_affineFunction_mod_four_eq_nonlinearity_mod_four_seven
        f hf bzero (Fin.cons (bzero + bone) a)
    have hcandidateDistance :
        hammingDistance f (pairedAffineFunctionSeven bzero bone a) = 56 := by
      rw [hammingDistance_pairedAffineFunctionSeven, hzeroDistance]
      have hpaired :
          hammingDistance f (pairedAffineFunctionSeven bzero bone a) =
            26 + hammingDistance (firstCoordinateSliceSeven f 1)
              (FABL.affineFunction bone a) := by
        rw [hammingDistance_pairedAffineFunctionSeven, hzeroDistance]
      change hammingDistance f (pairedAffineFunctionSeven bzero bone a) % 4 =
        nonlinearity f % 4 at hcandidateMod
      rw [hpaired, hnonlinearity] at hcandidateMod
      rw [hnonlinearity] at hcandidateLower
      change 56 ≤ hammingDistance f (pairedAffineFunctionSeven bzero bone a)
        at hcandidateLower
      rw [hpaired] at hcandidateLower
      omega
    exact ⟨bzero, bone, a, hcandidateDistance,
      pairedAffineFunctionSeven_error_zero_slice f bzero bone a x |>.trans
        hzeroPoint⟩
  · have hzeroEq : nonlinearity (firstCoordinateSliceSeven f 0) = 24 := by
      obtain ⟨bzero, a, hzeroDistance⟩ :=
        exists_affineFunction_hammingDistance_eq_nonlinearity
          (firstCoordinateSliceSeven f 0)
      obtain ⟨bone, honeDistance⟩ :=
        exists_affineFunction_same_slope_distance_le_thirty_two
          (firstCoordinateSliceSeven f 1) a
      have hcandidate :=
        nonlinearity_seven_le_slice_affine_distances f bzero bone a
      rw [hnonlinearity, hzeroDistance] at hcandidate
      omega
    have honeLower : 24 ≤ nonlinearity (firstCoordinateSliceSeven f 1) := by
      obtain ⟨bone, a, honeDistance⟩ :=
        exists_affineFunction_hammingDistance_eq_nonlinearity
          (firstCoordinateSliceSeven f 1)
      obtain ⟨bzero, hzeroDistance⟩ :=
        exists_affineFunction_same_slope_distance_le_thirty_two
          (firstCoordinateSliceSeven f 0) a
      have hcandidate :=
        nonlinearity_seven_le_slice_affine_distances f bzero bone a
      rw [hnonlinearity, honeDistance] at hcandidate
      omega
    have honeMod : nonlinearity (firstCoordinateSliceSeven f 1) % 4 = 0 := by
      obtain ⟨bzero, a, hzeroDistance⟩ :=
        exists_affineFunction_hammingDistance_eq_nonlinearity
          (firstCoordinateSliceSeven f 0)
      rw [hzeroEq] at hzeroDistance
      obtain ⟨bone, honeDistance⟩ :=
        exists_affineFunction_same_slope_distance_le_thirty_two
          (firstCoordinateSliceSeven f 1) a
      have hcandidate :=
        nonlinearity_seven_le_slice_affine_distances f bzero bone a
      rw [hnonlinearity, hzeroDistance] at hcandidate
      have honeDistanceEq :
          hammingDistance (firstCoordinateSliceSeven f 1)
            (FABL.affineFunction bone a) = 32 := by
        omega
      have hmod :=
        hammingDistance_affineFunction_mod_four_eq_nonlinearity_mod_four_six
          (firstCoordinateSliceSeven f 1) honeDegree bone a
      rw [honeDistanceEq] at hmod
      omega
    have honeUpper :=
      nonlinearity_six_le_twenty_eight (firstCoordinateSliceSeven f 1)
    have honeEq : nonlinearity (firstCoordinateSliceSeven f 1) = 24 := by
      by_cases hone : nonlinearity (firstCoordinateSliceSeven f 1) = 28
      · have hequality :=
          nonlinearity_seven_eq_slice_zero_add_twenty_eight f hone
        omega
      · omega
    obtain ⟨bone, a, honeDistance⟩ :=
      exists_affineFunction_hammingDistance_eq_nonlinearity
        (firstCoordinateSliceSeven f 1)
    rw [honeEq] at honeDistance
    obtain ⟨bzero, hzeroDistance⟩ :=
      exists_affineFunction_same_slope_distance_le_thirty_two
        (firstCoordinateSliceSeven f 0) a
    have hcandidate :=
      nonlinearity_seven_le_slice_affine_distances f bzero bone a
    rw [hnonlinearity, honeDistance] at hcandidate
    have hzeroDistanceEq :
        hammingDistance (firstCoordinateSliceSeven f 0)
          (FABL.affineFunction bzero a) = 32 := by
      omega
    by_cases hpoint :
        (firstCoordinateSliceSeven f 0 + FABL.affineFunction bzero a) x = 1
    · refine ⟨bzero, bone, a, ?_, ?_⟩
      · rw [hammingDistance_pairedAffineFunctionSeven,
          hzeroDistanceEq, honeDistance]
      · rw [pairedAffineFunctionSeven_error_zero_slice]
        exact hpoint
    · have hpointZero :
          (firstCoordinateSliceSeven f 0 + FABL.affineFunction bzero a) x = 0 := by
        by_contra hne
        exact hpoint (Fin.eq_one_of_ne_zero _ hne)
      have hcomplementSum := hammingDistance_affineFunction_add_one_sum_six
        (firstCoordinateSliceSeven f 0) bzero a
      have hcomplementDistance :
          hammingDistance (firstCoordinateSliceSeven f 0)
            (FABL.affineFunction (bzero + 1) a) = 32 := by
        omega
      refine ⟨bzero + 1, bone, a, ?_, ?_⟩
      · rw [hammingDistance_pairedAffineFunctionSeven,
          hcomplementDistance, honeDistance]
      · rw [pairedAffineFunctionSeven_error_zero_slice]
        change firstCoordinateSliceSeven f 0 x +
            ((bzero + 1) + FABL.f₂DotProduct a x) = 1
        change firstCoordinateSliceSeven f 0 x +
            (bzero + FABL.f₂DotProduct a x) = 0 at hpointZero
        calc
          firstCoordinateSliceSeven f 0 x +
              ((bzero + 1) + FABL.f₂DotProduct a x) =
              (firstCoordinateSliceSeven f 0 x +
                (bzero + FABL.f₂DotProduct a x)) + 1 := by ring
          _ = 1 := by rw [hpointZero]; simp

private theorem transport_minimum_affine_error_one_of_comp_affineEquiv
    (f : BooleanFunction 7)
    (L : FABL.F₂Cube 7 ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube 7)
    (x : FABL.F₂Cube 7) (b : FABL.𝔽₂) (a : FABL.F₂Cube 7)
    (hdistance :
      hammingDistance (f ∘ L) (FABL.affineFunction b a) = 56)
    (hpoint :
      ((f ∘ L) + FABL.affineFunction b a) (L.symm x) = 1) :
    ∃ c d, hammingDistance f (FABL.affineFunction c d) = 56 ∧
      (f + FABL.affineFunction c d) x = 1 := by
  obtain ⟨c, d, haffine⟩ :=
    exists_affineFunction_comp_affineEquiv b a L.symm
  refine ⟨c, d, ?_, ?_⟩
  · rw [← haffine]
    have hcancel : (f ∘ L) ∘ L.symm = f := by
      funext y
      simp
    have hinvariant := hammingDistance_comp_affineEquiv
      (f ∘ L) (FABL.affineFunction b a) L.symm
    rw [← hcancel]
    exact hinvariant.trans hdistance
  · rw [← haffine]
    simpa only [Pi.add_apply, Function.comp_apply, L.apply_symm_apply] using hpoint

private def firstCoordinateToggleSeven :
    FABL.F₂Cube 7 ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube 7 :=
  AffineEquiv.constVAdd FABL.𝔽₂ (FABL.F₂Cube 7)
    (Pi.single 0 1 : FABL.F₂Cube 7)

private theorem firstCoordinateToggleSeven_apply
    (x : FABL.F₂Cube 7) :
    firstCoordinateToggleSeven x = x + Pi.single 0 1 := by
  funext i
  simp [firstCoordinateToggleSeven, add_comm]

private theorem firstCoordinateToggleSeven_symm_apply
    (x : FABL.F₂Cube 7) :
    firstCoordinateToggleSeven.symm x = x + Pi.single 0 1 := by
  funext i
  simp [firstCoordinateToggleSeven, add_comm]

private theorem firstCoordinateSliceSeven_comp_toggle_zero
    (f : BooleanFunction 7) :
    firstCoordinateSliceSeven (f ∘ firstCoordinateToggleSeven) 0 =
      firstCoordinateSliceSeven f 1 := by
  funext x
  change f (firstCoordinateToggleSeven (Fin.cons 0 x)) = f (Fin.cons 1 x)
  rw [firstCoordinateToggleSeven_apply]
  apply congrArg f
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

private theorem firstCoordinateSliceSeven_comp_toggle_one
    (f : BooleanFunction 7) :
    firstCoordinateSliceSeven (f ∘ firstCoordinateToggleSeven) 1 =
      firstCoordinateSliceSeven f 0 := by
  funext x
  change f (firstCoordinateToggleSeven (Fin.cons 1 x)) = f (Fin.cons 0 x)
  rw [firstCoordinateToggleSeven_apply]
  apply congrArg f
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

private theorem exists_minimum_affine_error_one_at_of_slices_degree_le_four
    (f : BooleanFunction 7)
    (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (hzeroDegree :
      FABL.functionAlgebraicDegree (firstCoordinateSliceSeven f 0) ≤ 4)
    (honeDegree :
      FABL.functionAlgebraicDegree (firstCoordinateSliceSeven f 1) ≤ 4)
    (hnonlinearity : nonlinearity f = 56)
    (x : FABL.F₂Cube 7) :
    ∃ b a, hammingDistance f (FABL.affineFunction b a) = 56 ∧
      (f + FABL.affineFunction b a) x = 1 := by
  by_cases hxzero : x 0 = 0
  · have hxcons : Fin.cons 0 (Fin.tail x) = x := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact hxzero.symm
      · rfl
    obtain ⟨bzero, bone, a, hdistance, hpoint⟩ :=
      exists_minimum_pairedAffineFunction_error_one_at_zero_slice
        f hf hzeroDegree honeDegree hnonlinearity (Fin.tail x)
    refine ⟨bzero, Fin.cons (bzero + bone) a, ?_, ?_⟩
    · exact hdistance
    · simpa only [pairedAffineFunctionSeven, hxcons] using hpoint
  · have hxone : x 0 = 1 := Fin.eq_one_of_ne_zero _ hxzero
    let g : BooleanFunction 7 := f ∘ firstCoordinateToggleSeven
    let y : FABL.F₂Cube 7 := firstCoordinateToggleSeven.symm x
    have hyzero : y 0 = 0 := by
      rw [show y = x + Pi.single 0 1 by
        exact firstCoordinateToggleSeven_symm_apply x]
      simp [hxone]
    have hycons : Fin.cons 0 (Fin.tail y) = y := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact hyzero.symm
      · rfl
    have hgDegree : FABL.functionAlgebraicDegree g ≤ 5 := by
      have hcomp : g = f ∘ firstCoordinateToggleSeven := rfl
      rw [hcomp, FABL.functionAlgebraicDegree_comp_affineEquiv]
      exact hf
    have hgzeroDegree :
        FABL.functionAlgebraicDegree (firstCoordinateSliceSeven g 0) ≤ 4 := by
      rw [show firstCoordinateSliceSeven g 0 =
          firstCoordinateSliceSeven f 1 by
        exact firstCoordinateSliceSeven_comp_toggle_zero f]
      exact honeDegree
    have hgoneDegree :
        FABL.functionAlgebraicDegree (firstCoordinateSliceSeven g 1) ≤ 4 := by
      rw [show firstCoordinateSliceSeven g 1 =
          firstCoordinateSliceSeven f 0 by
        exact firstCoordinateSliceSeven_comp_toggle_one f]
      exact hzeroDegree
    have hgNonlinearity : nonlinearity g = 56 := by
      have hinvariant :=
        nonlinearity_comp_affineEquiv f firstCoordinateToggleSeven
      change nonlinearity g = nonlinearity f at hinvariant
      rwa [hnonlinearity] at hinvariant
    obtain ⟨bzero, bone, a, hdistance, hpoint⟩ :=
      exists_minimum_pairedAffineFunction_error_one_at_zero_slice
        g hgDegree hgzeroDegree hgoneDegree hgNonlinearity (Fin.tail y)
    have hpointY :
        (g + pairedAffineFunctionSeven bzero bone a) y = 1 := by
      simpa only [hycons] using hpoint
    exact transport_minimum_affine_error_one_of_comp_affineEquiv
      f firstCoordinateToggleSeven x bzero (Fin.cons (bzero + bone) a)
      (by simpa [g, pairedAffineFunctionSeven] using hdistance)
      (by simpa [g, y, pairedAffineFunctionSeven] using hpointY)

/-- A seven-variable degree-at-most-five coset at nonlinearity `56` has,
through every coordinate, a minimum-weight representative modulo the
first-order Reed--Muller code. -/
theorem exists_minimum_affine_error_one_at_of_degree_le_five_nonlinearity_eq_56_seven
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5)
    (hnonlinearity : nonlinearity f = 56) (x : FABL.F₂Cube 7) :
    ∃ b a, hammingDistance f (FABL.affineFunction b a) = 56 ∧
      (f + FABL.affineFunction b a) x = 1 := by
  obtain ⟨P, hzero, hone⟩ :=
    exists_linearEquiv_firstCoordinateSlices_degree_le_four f hf
  let g : BooleanFunction 7 := f ∘ P
  let y : FABL.F₂Cube 7 := P.toAffineEquiv.symm x
  have hgDegree : FABL.functionAlgebraicDegree g ≤ 5 := by
    have hcomp : g = f ∘ P.toAffineEquiv := rfl
    rw [hcomp, FABL.functionAlgebraicDegree_comp_affineEquiv]
    exact hf
  have hgNonlinearity : nonlinearity g = 56 := by
    have hinvariant := nonlinearity_comp_affineEquiv f P.toAffineEquiv
    change nonlinearity g = nonlinearity f at hinvariant
    rwa [hnonlinearity] at hinvariant
  obtain ⟨b, a, hdistance, hpoint⟩ :=
    exists_minimum_affine_error_one_at_of_slices_degree_le_four
      g hgDegree (by simpa [g] using hzero) (by simpa [g] using hone)
      hgNonlinearity y
  exact transport_minimum_affine_error_one_of_comp_affineEquiv
    f P.toAffineEquiv x b a
    (by simpa [g] using hdistance)
    (by simpa [g, y] using hpoint)

end CryptBoolean
