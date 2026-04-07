/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Coefficients for the Dedekind zeta function

This file packages the coefficients of `NumberField.dedekindZeta` as an arithmetic function.
The eventual goal is to prove multiplicativity and derive an Euler product.
-/

@[expose] public section

noncomputable section

open Filter
open scoped LSeries.notation

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The fiber of the absolute norm map over `n`. -/
def NormFiber (n : ℕ) := {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- The arithmetic function counting integral ideals of a given absolute norm. -/
noncomputable def idealNormCount : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  map_zero' := rfl

@[simp]
theorem idealNormCount_zero : idealNormCount K 0 = 0 :=
  rfl

theorem idealNormCount_apply_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    idealNormCount K n = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
  simp [idealNormCount, hn]

theorem isCoprime_of_coprime_absNorm {I J : Ideal (𝓞 K)}
    (hIJ : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J)) :
    IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I ⊔ J) hsup
  have hMI : I ≤ M := le_trans le_sup_left hle
  have hMJ : J ≤ M := le_trans le_sup_right hle
  have hdvd : Ideal.absNorm M ∣ Nat.gcd (Ideal.absNorm I) (Ideal.absNorm J) :=
    Nat.dvd_gcd (Ideal.absNorm_dvd_absNorm_of_le hMI) (Ideal.absNorm_dvd_absNorm_of_le hMJ)
  have hnormM : Ideal.absNorm M = 1 := by
    rw [hIJ.gcd_eq_one] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  exact hM.ne_top ((Ideal.absNorm_eq_one_iff).mp hnormM)

/-- The rational prime lying under a height-one prime of `𝓞 K`. -/
noncomputable def ratPrime (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℕ :=
  Ideal.absNorm (Ideal.under ℤ v.asIdeal)

omit [NumberField K] in
theorem ratPrime_prime (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (ratPrime K v).Prime := by
  letI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  simpa [ratPrime] using Nat.absNorm_under_prime v.asIdeal

theorem absNorm_maxPowDividing_dvd (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Ideal.absNorm (v.maxPowDividing I) ∣ Ideal.absNorm I := by
  have hdiv : v.maxPowDividing I ∣
      ∏ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), w.maxPowDividing I :=
    finprod_mem_dvd v (Ideal.hasFiniteMulSupport hI)
  rw [Ideal.finprod_heightOneSpectrum_factorization hI] at hdiv
  exact map_dvd Ideal.absNorm hdiv

/-- The `m`-part of an ideal, split according to the rational prime below each height-one prime. -/
noncomputable def splitIdealLeft (I : Ideal (𝓞 K)) (m : ℕ) : Ideal (𝓞 K) :=
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    if ratPrime K v ∣ m then v.maxPowDividing I else 1

/-- The `n`-part of an ideal, split according to the rational prime below each height-one prime. -/
noncomputable def splitIdealRight (I : Ideal (𝓞 K)) (n : ℕ) : Ideal (𝓞 K) :=
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    if ratPrime K v ∣ n then v.maxPowDividing I else 1

theorem absNorm_maxPowDividing_is_prime_pow (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ e : ℕ, Ideal.absNorm (v.maxPowDividing I) = ratPrime K v ^ e := by
  classical
  letI : v.asIdeal.LiesOver (Ideal.span {(ratPrime K v : ℤ)}) := Int.liesOver_span_absNorm v.asIdeal
  refine ⟨(Ideal.span {(ratPrime K v : ℤ)}).inertiaDeg v.asIdeal *
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
  rw [v.maxPowDividing_eq_pow_multiset_count (I := I) hI, map_pow,
    Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal (ratPrime_prime K v), pow_mul]
  rfl

theorem splitIdeal_mul {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥) (hmn : Nat.Coprime m n)
    (hNorm : Ideal.absNorm I = m * n) :
    splitIdealLeft K I m * splitIdealRight K I n = I := by
  classical
  let f : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Ideal (𝓞 K) := fun v ↦ v.maxPowDividing I
  let s : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := {v | ratPrime K v ∣ m}
  let t : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := {v | ratPrime K v ∣ n}
  have hf : Function.HasFiniteMulSupport f := Ideal.hasFiniteMulSupport hI
  have hf_left : Function.HasFiniteMulSupport (s.mulIndicator f) := by
    refine hf.subset ?_
    rw [Set.mulSupport_mulIndicator]
    exact Set.inter_subset_right
  have hf_right : Function.HasFiniteMulSupport (sᶜ.mulIndicator f) := by
    refine hf.subset ?_
    rw [Set.mulSupport_mulIndicator]
    exact Set.inter_subset_right
  have hleft :
      splitIdealLeft K I m = ∏ᶠ v ∈ s, f v := by
    rw [splitIdealLeft, finprod_mem_def]
    apply finprod_congr
    intro v
    simp [f, s, Set.mulIndicator_apply]
  have hright :
      splitIdealRight K I n = ∏ᶠ v ∈ t, f v := by
    rw [splitIdealRight, finprod_mem_def]
    apply finprod_congr
    intro v
    simp [f, t, Set.mulIndicator_apply]
  have hts :
      ∏ᶠ v ∈ t, f v = ∏ᶠ v ∈ sᶜ, f v := by
    apply finprod_mem_inter_mulSupport_eq' (f := f) (s := t) (t := sᶜ)
    intro v hv
    constructor
    · intro hvn
      simp [s]
      intro hvm
      have hcop : Nat.Coprime (ratPrime K v) n := Nat.Coprime.of_dvd_left hvm hmn
      exact ((ratPrime_prime K v).coprime_iff_not_dvd.mp hcop) hvn
    · intro hvm
      have hcount_pos :
          0 < Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) := by
        have hv' : f v ≠ 1 := by
          simpa [Function.mem_mulSupport] using hv
        by_contra hcount
        apply hv'
        rw [show f v =
            v.asIdeal ^ Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) by
          simpa [f] using v.maxPowDividing_eq_pow_multiset_count (I := I) hI,
          Nat.eq_zero_of_not_pos hcount]
        simp
      have hle : v.maxPowDividing I ≤ v.asIdeal := by
        rw [v.maxPowDividing_eq_pow_multiset_count (I := I) hI]
        simpa using
          (Ideal.pow_le_pow_right hcount_pos :
            v.asIdeal ^
                Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) ≤
              v.asIdeal ^ 1)
      have hpdvdnorm : ratPrime K v ∣ Ideal.absNorm (f v) := by
        exact dvd_trans
          (by simpa [ratPrime] using Int.absNorm_under_dvd_absNorm (I := v.asIdeal))
          (Ideal.absNorm_dvd_absNorm_of_le hle)
      have hpdvdmn : ratPrime K v ∣ m * n := dvd_trans hpdvdnorm (hNorm ▸ absNorm_maxPowDividing_dvd K v hI)
      rcases (ratPrime_prime K v).dvd_mul.mp hpdvdmn with hpm | hpn
      · exact False.elim (hvm hpm)
      · exact hpn
  calc
    splitIdealLeft K I m * splitIdealRight K I n
        = (∏ᶠ v ∈ s, f v) * (∏ᶠ v ∈ sᶜ, f v) := by rw [hleft, hright, hts]
    _ = (∏ᶠ v, s.mulIndicator f v) * (∏ᶠ v, sᶜ.mulIndicator f v) := by
      rw [← finprod_mem_def, ← finprod_mem_def]
    _ = ∏ᶠ v, s.mulIndicator f v * sᶜ.mulIndicator f v := by
      rw [← finprod_mul_distrib hf_left hf_right]
    _ = ∏ᶠ v, f v := by
      apply finprod_congr
      intro v
      simpa [Set.mulIndicator_apply] using
        congrFun (Set.mulIndicator_mul_compl_eq_piecewise (s := s) (f := f) (g := f)) v
    _ = I := Ideal.finprod_heightOneSpectrum_factorization hI

theorem splitIdealLeft_absNorm_coprime_right {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥)
    (hmn : Nat.Coprime m n) :
    Nat.Coprime (Ideal.absNorm (splitIdealLeft K I m)) n := by
  rw [splitIdealLeft]
  have habs :
      Ideal.absNorm (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          if ratPrime K v ∣ m then v.maxPowDividing I else 1) =
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Ideal.absNorm (if ratPrime K v ∣ m then v.maxPowDividing I else 1) := by
    simpa using
      (Ideal.absNorm.toMonoidHom.map_finprod_of_preimage_one
        (fun J hJ => by simpa using (Ideal.absNorm_eq_one_iff.mp hJ))
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          if ratPrime K v ∣ m then v.maxPowDividing I else 1))
  rw [habs]
  refine finprod_induction
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Ideal.absNorm (if ratPrime K v ∣ m then v.maxPowDividing I else 1))
    (p := fun a : ℕ => Nat.Coprime a n)
    (by simp)
    (fun a b ha hb => ha.mul_left hb)
    ?_
  intro v
  by_cases hv : ratPrime K v ∣ m
  · have hcop : Nat.Coprime (ratPrime K v) n := Nat.Coprime.of_dvd_left hv hmn
    obtain ⟨e, he⟩ := absNorm_maxPowDividing_is_prime_pow K v hI
    simpa [hv, he] using hcop.pow_left e
  · simp [hv]

theorem splitIdealRight_absNorm_coprime_left {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥)
    (hmn : Nat.Coprime m n) :
    Nat.Coprime m (Ideal.absNorm (splitIdealRight K I n)) := by
  rw [splitIdealRight]
  have habs :
      Ideal.absNorm (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          if ratPrime K v ∣ n then v.maxPowDividing I else 1) =
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Ideal.absNorm (if ratPrime K v ∣ n then v.maxPowDividing I else 1) := by
    simpa using
      (Ideal.absNorm.toMonoidHom.map_finprod_of_preimage_one
        (fun J hJ => by simpa using (Ideal.absNorm_eq_one_iff.mp hJ))
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          if ratPrime K v ∣ n then v.maxPowDividing I else 1))
  rw [habs]
  refine finprod_induction
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Ideal.absNorm (if ratPrime K v ∣ n then v.maxPowDividing I else 1))
    (p := fun a : ℕ => Nat.Coprime m a)
    (by simp)
    (fun a b ha hb => ha.mul_right hb)
    ?_
  intro v
  by_cases hv : ratPrime K v ∣ n
  · have hcop : Nat.Coprime m (ratPrime K v) := Nat.Coprime.of_dvd_right hv hmn
    obtain ⟨e, he⟩ := absNorm_maxPowDividing_is_prime_pow K v hI
    simpa [hv, he] using hcop.pow_right e
  · simp [hv]

theorem splitIdealLeft_absNorm_eq {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥) (hmn : Nat.Coprime m n)
    (hNorm : Ideal.absNorm I = m * n) :
    Ideal.absNorm (splitIdealLeft K I m) = m := by
  let a := Ideal.absNorm (splitIdealLeft K I m)
  let b := Ideal.absNorm (splitIdealRight K I n)
  have hab : a * b = m * n := by
    dsimp [a, b]
    simpa [map_mul, hNorm] using congrArg Ideal.absNorm (splitIdeal_mul K hI hmn hNorm)
  have ha_coprime : Nat.Coprime a n := by
    simpa [a] using splitIdealLeft_absNorm_coprime_right K hI hmn
  have hm_dvd_a : m ∣ a := by
    have hm_dvd_ab : m ∣ a * b := by
      rw [hab]
      exact dvd_mul_right m n
    have hb_coprime : Nat.Coprime m b := by
      simpa [b] using splitIdealRight_absNorm_coprime_left K hI hmn
    exact hb_coprime.dvd_of_dvd_mul_right hm_dvd_ab
  have ha_dvd_m : a ∣ m := by
    have ha_dvd_mn : a ∣ m * n := by
      exact Dvd.intro b hab
    exact ha_coprime.dvd_of_dvd_mul_right ha_dvd_mn
  exact Nat.dvd_antisymm ha_dvd_m hm_dvd_a

theorem splitIdealRight_absNorm_eq {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥) (hmn : Nat.Coprime m n)
    (hNorm : Ideal.absNorm I = m * n) :
    Ideal.absNorm (splitIdealRight K I n) = n := by
  let a := Ideal.absNorm (splitIdealLeft K I m)
  let b := Ideal.absNorm (splitIdealRight K I n)
  have hab : a * b = m * n := by
    dsimp [a, b]
    simpa [map_mul, hNorm] using congrArg Ideal.absNorm (splitIdeal_mul K hI hmn hNorm)
  have hb_coprime : Nat.Coprime m b := by
    simpa [b] using splitIdealRight_absNorm_coprime_left K hI hmn
  have hn_dvd_b : n ∣ b := by
    have hn_dvd_ab : n ∣ a * b := by
      rw [hab]
      exact dvd_mul_left n m
    have ha_coprime : Nat.Coprime a n := by
      simpa [a] using splitIdealLeft_absNorm_coprime_right K hI hmn
    exact ha_coprime.symm.dvd_of_dvd_mul_left hn_dvd_ab
  have hb_dvd_n : b ∣ n := by
    have hb_dvd_mn : b ∣ m * n := by
      exact Dvd.intro a (by simpa [Nat.mul_comm] using hab)
    exact hb_coprime.symm.dvd_of_dvd_mul_left hb_dvd_mn
  exact Nat.dvd_antisymm hb_dvd_n hn_dvd_b

/-- Multiplication of ideals induces a map on fibers of the absolute norm. -/
def mulOnAbsNormFiber (m n : ℕ) :
    NormFiber K m → NormFiber K n → NormFiber K (m * n) :=
  fun ⟨I, hI⟩ ⟨J, hJ⟩ => ⟨I * J, by
    rw [map_mul, hI, hJ]⟩

@[simp]
theorem mulOnAbsNormFiber_fst (m n : ℕ)
    (I : NormFiber K m) (J : NormFiber K n) :
    (mulOnAbsNormFiber K m n I J).1 = I.1 * J.1 :=
  rfl

def mulOnAbsNormFiberProd (m n : ℕ) :
    NormFiber K m × NormFiber K n → NormFiber K (m * n) :=
  fun IJ => mulOnAbsNormFiber K m n IJ.1 IJ.2

def splitNormFiber {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    NormFiber K (m * n) → NormFiber K m × NormFiber K n :=
  fun I =>
    let J := I.1
    let hJ : J ≠ ⊥ := by
      intro hbot
      have hmn0 : m * n = 0 := by
        have hnorm : Ideal.absNorm J = m * n := I.2
        simpa [J, hbot] using hnorm.symm
      rcases Nat.mul_eq_zero.mp hmn0 with h0 | h0
      · exact False.elim (hm h0)
      · exact False.elim (hn h0)
    (⟨splitIdealLeft K J m, splitIdealLeft_absNorm_eq K hJ h I.2⟩,
      ⟨splitIdealRight K J n, splitIdealRight_absNorm_eq K hJ h I.2⟩)

theorem splitNormFiber_leftInverse {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    Function.LeftInverse (splitNormFiber K hm hn h) (mulOnAbsNormFiberProd K m n) := by
  intro IJ
  rcases IJ with ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    change splitIdealLeft K (I * J) m = I
    have hI0 : I ≠ ⊥ := by
      intro hbot
      exact hm (by simpa [hbot] using hI.symm)
    have hJ0 : J ≠ ⊥ := by
      intro hbot
      exact hn (by simpa [hbot] using hJ.symm)
    have hIJ : I * J ≠ ⊥ := by
      exact mul_ne_zero hI0 hJ0
    have hmul : Ideal.absNorm (I * J) = m * n := by simp [map_mul, hI, hJ]
    have hsplit_mul := splitIdeal_mul K hIJ h hmul
    have hcop_leftJ : Nat.Coprime (Ideal.absNorm (splitIdealLeft K (I * J) m)) (Ideal.absNorm J) := by
      simpa [hJ] using splitIdealLeft_absNorm_coprime_right K hIJ h
    have hcopIdeals_leftJ : IsCoprime (splitIdealLeft K (I * J) m) J :=
      isCoprime_of_coprime_absNorm K hcop_leftJ
    have hleft_dvd_prod : splitIdealLeft K (I * J) m ∣ I * J := by
      refine ⟨splitIdealRight K (I * J) n, hsplit_mul.symm⟩
    have hleft_dvd_I : splitIdealLeft K (I * J) m ∣ I :=
      hcopIdeals_leftJ.dvd_of_dvd_mul_right hleft_dvd_prod
    have hcop_Iright : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm (splitIdealRight K (I * J) n)) := by
      simpa [hI] using splitIdealRight_absNorm_coprime_left K hIJ h
    have hcopIdeals_Iright : IsCoprime I (splitIdealRight K (I * J) n) :=
      isCoprime_of_coprime_absNorm K hcop_Iright
    have hI_dvd_prod : I ∣ I * J := ⟨J, rfl⟩
    have hI_dvd_left : I ∣ splitIdealLeft K (I * J) m := by
      rw [← hsplit_mul] at hI_dvd_prod
      exact hcopIdeals_Iright.dvd_of_dvd_mul_right hI_dvd_prod
    exact le_antisymm (Ideal.dvd_iff_le.mp hI_dvd_left) (Ideal.dvd_iff_le.mp hleft_dvd_I)
  · apply Subtype.ext
    change splitIdealRight K (I * J) n = J
    have hI0 : I ≠ ⊥ := by
      intro hbot
      exact hm (by simpa [hbot] using hI.symm)
    have hJ0 : J ≠ ⊥ := by
      intro hbot
      exact hn (by simpa [hbot] using hJ.symm)
    have hIJ : I * J ≠ ⊥ := by
      exact mul_ne_zero hI0 hJ0
    have hmul : Ideal.absNorm (I * J) = m * n := by simp [map_mul, hI, hJ]
    have hsplit_mul := splitIdeal_mul K hIJ h hmul
    have hcop_Iright : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm (splitIdealRight K (I * J) n)) := by
      simpa [hI] using splitIdealRight_absNorm_coprime_left K hIJ h
    have hcopIdeals_Iright : IsCoprime I (splitIdealRight K (I * J) n) :=
      isCoprime_of_coprime_absNorm K hcop_Iright
    have hright_dvd_prod : splitIdealRight K (I * J) n ∣ I * J := by
      rw [mul_comm] at hsplit_mul
      refine ⟨splitIdealLeft K (I * J) m, hsplit_mul.symm⟩
    have hright_dvd_J : splitIdealRight K (I * J) n ∣ J :=
      hcopIdeals_Iright.symm.dvd_of_dvd_mul_left hright_dvd_prod
    have hcop_leftJ : Nat.Coprime (Ideal.absNorm (splitIdealLeft K (I * J) m)) (Ideal.absNorm J) := by
      simpa [hJ] using splitIdealLeft_absNorm_coprime_right K hIJ h
    have hcopIdeals_leftJ : IsCoprime (splitIdealLeft K (I * J) m) J :=
      isCoprime_of_coprime_absNorm K hcop_leftJ
    have hJ_dvd_prod : J ∣ I * J := ⟨I, by ac_rfl⟩
    have hJ_dvd_right : J ∣ splitIdealRight K (I * J) n := by
      rw [← hsplit_mul] at hJ_dvd_prod
      exact hcopIdeals_leftJ.symm.dvd_of_dvd_mul_left hJ_dvd_prod
    exact le_antisymm (Ideal.dvd_iff_le.mp hJ_dvd_right) (Ideal.dvd_iff_le.mp hright_dvd_J)

theorem splitNormFiber_rightInverse {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    Function.RightInverse (splitNormFiber K hm hn h) (mulOnAbsNormFiberProd K m n) := by
  intro I
  apply Subtype.ext
  simp [splitNormFiber, mulOnAbsNormFiberProd, mulOnAbsNormFiber]
  let J := I.1
  have hJ : J ≠ ⊥ := by
    intro hbot
    have hmn0 : m * n = 0 := by
      have hnorm : Ideal.absNorm J = m * n := I.2
      simpa [J, hbot] using hnorm.symm
    rcases Nat.mul_eq_zero.mp hmn0 with h0 | h0
    · exact False.elim (hm h0)
    · exact False.elim (hn h0)
  exact splitIdeal_mul K hJ h I.2

noncomputable def normFiberEquivProd {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    NormFiber K (m * n) ≃ NormFiber K m × NormFiber K n where
  toFun := splitNormFiber K hm hn h
  invFun := mulOnAbsNormFiberProd K m n
  left_inv := splitNormFiber_rightInverse K hm hn h
  right_inv := splitNormFiber_leftInverse K hm hn h

theorem idealNormCount_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    idealNormCount K (m * n) = idealNormCount K m * idealNormCount K n := by
  by_cases hm : m = 0
  · subst hm
    simp
  by_cases hn : n = 0
  · subst hn
    simp
  rw [idealNormCount_apply_of_ne_zero K (Nat.mul_ne_zero hm hn),
    idealNormCount_apply_of_ne_zero K hm, idealNormCount_apply_of_ne_zero K hn,
    ← Nat.card_prod]
  exact Nat.card_congr (normFiberEquivProd K hm hn h)

theorem idealNormCount_isMultiplicative : (idealNormCount K).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [idealNormCount_apply_of_ne_zero K one_ne_zero]
    simp [Ideal.absNorm_eq_one_iff]
  · intro m n h
    exact idealNormCount_mul_of_coprime K h

noncomputable def dedekindZetaSummand (s : ℂ) : ArithmeticFunction ℂ where
  toFun n := LSeries.term (fun n ↦ (idealNormCount K n : ℂ)) s n
  map_zero' := LSeries.term_zero _ _

theorem dedekindZetaSummand_apply (s : ℂ) (n : ℕ) :
    dedekindZetaSummand K s n = LSeries.term (fun n ↦ (idealNormCount K n : ℂ)) s n :=
  rfl

theorem dedekindZetaSummand_isMultiplicative (s : ℂ) :
    (dedekindZetaSummand K s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · simp [dedekindZetaSummand, LSeries.term_def₀, idealNormCount_isMultiplicative]
  · intro m n hm hn hmn
    have hpow : ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
      simpa only [Nat.cast_mul, Complex.ofReal_natCast]
        using Complex.mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg (-s)
    rw [dedekindZetaSummand_apply, dedekindZetaSummand_apply, dedekindZetaSummand_apply,
      LSeries.term_def₀ (by simp),
      LSeries.term_def₀ (by simp),
      LSeries.term_def₀ (by simp),
      (idealNormCount_isMultiplicative K).2 hmn, hpow]
    simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

theorem summable_dedekindZetaSummand (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n ↦ ‖dedekindZetaSummand K s n‖) := by
  have hO :
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormCount K k : ℝ)) =O[atTop]
        fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    have hlim :
        Tendsto (fun n : ℕ =>
          (∑ k ∈ Finset.Icc 1 n, (idealNormCount K k : ℝ)) / ((n : ℝ) ^ (1 : ℝ))) atTop
          (nhds ((2 ^ InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^
            InfinitePlace.nrComplexPlaces K * Units.regulator K * classNumber K) /
            (Units.torsionOrder K * Real.sqrt |discr K|) : ℝ)) := by
      simpa [Real.rpow_one] using
        (((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ by
          simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
          congr
          conv_rhs =>
            rw [Finset.sum_congr rfl fun k hk ↦ idealNormCount_apply_of_ne_zero K
              (Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1)]
          rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
            show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
            show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
              have hfinite : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} := by
                exact Ideal.finite_setOf_absNorm_eq 0
              letI := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = 0}
              rw [Nat.card_eq_fintype_card]
              simp [Ideal.absNorm_eq_zero_iff],
            Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
            ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
          simp [Set.coe_eq_subtype])
    exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (a := ((2 ^
      InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K *
      Units.regulator K * classNumber K) / (Units.torsionOrder K * Real.sqrt |discr K|) : ℝ)) hlim
  have hS :
      LSeriesSummable (fun n ↦ (idealNormCount K n : ℝ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _)
      (show (0 : ℝ) ≤ 1 by norm_num) hs
  rw [LSeriesSummable, ← summable_norm_iff] at hS
  simpa [dedekindZetaSummand_apply] using hS

theorem tsum_dedekindZetaSummand (s : ℂ) :
    ∑' n : ℕ, dedekindZetaSummand K s n = dedekindZeta K s := by
  rw [NumberField.dedekindZeta, LSeries]
  refine tsum_congr fun n ↦ ?_
  by_cases hn : n = 0
  · simp [dedekindZetaSummand, hn]
  · simp [dedekindZetaSummand, LSeries.term_def, idealNormCount_apply_of_ne_zero K hn, hn]

theorem dedekindZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    Filter.Tendsto (fun n : ℕ ↦ ∏ p ∈ Nat.primesBelow n, ∑' e : ℕ, dedekindZetaSummand K s (p ^ e))
      atTop (nhds (dedekindZeta K s)) := by
  rw [← tsum_dedekindZetaSummand K s]
  exact ArithmeticFunction.IsMultiplicative.eulerProduct
    (dedekindZetaSummand_isMultiplicative K s) (summable_dedekindZetaSummand K s hs)

theorem dedekindZeta_eq_LSeries_idealNormCount (s : ℂ) :
    dedekindZeta K s = LSeries (fun n ↦ (idealNormCount K n : ℂ)) s := by
  refine LSeries_congr (s := s) ?_
  intro n hn
  rw [idealNormCount_apply_of_ne_zero K hn]

end NumberField
