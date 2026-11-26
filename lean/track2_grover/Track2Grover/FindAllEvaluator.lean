/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module
public import Mathlib.Data.Nat.Basic

namespace QuantumComputation.Specs.DickeSol
@[expose] public section

def rkm128kWordBits (k w : ℕ) : List Bool :=
  match k with
  | 0 => []
  | k' + 1 =>
    Nat.beq (Nat.mod w 2) 1 :: rkm128kWordBits k' (Nat.div w 2)

structure Rkm128kSeg where
  /-- Block multiplicity `l_s` (`1 <= l_s <= lTableMax`, non-decreasing across segments). -/
  lS : ℕ
  /-- `10 ^ 9`-scaled duration `tau9` (`1 <= tau9 <= 4 * 10 ^ 9`). -/
  tau9 : ℕ
  /-- Macro-substep count `nSub` (`1 <= nSub <= 16384`). -/
  nSub : ℕ
  /-- Per-substep polynomial degree `degP` (`1 <= degP <= 64`). -/
  degP : ℕ
  /-- Orbital prefix-kick sign mask applied at segment end. -/
  mask : List Bool

def primNatBlt (a b : ℕ) : Bool :=
  Nat.ble (Nat.add a 1) b

def wdScale : ℕ := 1000000000000000

def highdStrictConsInt (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat n =>
    match Nat.add 1 n with
    | 0 =>
      match xs with
      | [] => [Int.ofNat 0]
      | h :: t => Int.ofNat 0 :: h :: t
    | v + 1 =>
      match xs with
      | [] => [Int.ofNat v]
      | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc n =>
    match Nat.add 1 n with
    | 0 =>
      match xs with
      | [] => [Int.negSucc 0]
      | h :: t => Int.negSucc 0 :: h :: t
    | v + 1 =>
      match xs with
      | [] => [Int.negSucc v]
      | h :: t => Int.negSucc v :: h :: t

def primIntNatAbs : ℤ → ℕ
  | Int.ofNat m => m
  | Int.negSucc m => Nat.add m 1

namespace AltForce
def withForcedNat {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  match Nat.add 1 x with
  | 0 => k 0
  | v + 1 => k v
end AltForce

def strictNatCons (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 =>
    match xs with
    | [] => [0]
    | h :: t => 0 :: h :: t
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t

namespace HighDForce
def withForcedNat {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  match Nat.add 1 x with
  | 0 => k 0
  | v + 1 => k v
end HighDForce

namespace HighDForce
def withForcedList {α β : Type} (xs : List α) (k : List α → β) : β :=
  match xs with
  | [] => k []
  | h :: t => k (h :: t)
end HighDForce

def highdNatMin (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

def rkmBoolListLen : List Bool → ℕ
  | [] => 0
  | _ :: bs => Nat.add 1 (rkmBoolListLen bs)

def altInitGuess (val : ℕ) : ℕ :=
  cond (Nat.ble val 16) 4000000000000000
    (cond (Nat.ble val 4096) 64000000000000000
      (cond (Nat.ble val 1048576) 1024000000000000000
        (cond (Nat.ble val 268435456) 16384000000000000000
          (cond (Nat.ble val 68719476736) 262144000000000000000
            67108864000000000000000))))

def strictConsInt (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat n =>
    match Nat.add 1 n with
    | 0 =>
      match xs with
      | [] => [Int.ofNat 0]
      | h :: t => Int.ofNat 0 :: h :: t
    | v + 1 =>
      match xs with
      | [] => [Int.ofNat v]
      | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc n =>
    match Nat.add 1 n with
    | 0 =>
      match xs with
      | [] => [Int.negSucc 0]
      | h :: t => Int.negSucc 0 :: h :: t
    | v + 1 =>
      match xs with
      | [] => [Int.negSucc v]
      | h :: t => Int.negSucc v :: h :: t

def altIntLen : List ℤ → ℕ
  | [] => 0
  | _ :: xs => Nat.add (altIntLen xs) 1

def muxRawNegOfNat : ℕ → ℤ
  | 0 => Int.ofNat 0
  | k + 1 => Int.negSucc k

def primOfNatForced (x : ℕ) : ℤ :=
  match Nat.add 1 x with
  | 0 => Int.ofNat 0
  | v + 1 => Int.ofNat v

def muxRawSubNatNat (m n : ℕ) : ℤ :=
  match Nat.sub n m with
  | 0 => Int.ofNat (Nat.sub m n)
  | k + 1 => Int.negSucc k

def primNegSuccForced (x : ℕ) : ℤ :=
  match Nat.add 1 x with
  | 0 => Int.negSucc 0
  | v + 1 => Int.negSucc v

def altListLen : List ℕ → ℕ
  | [] => 0
  | _ :: xs => Nat.add (altListLen xs) 1

def rkmColdR2NumDen (m : ℕ) : ℕ × ℕ :=
  cond (Nat.beq m 2)
    (666702407513, 1000000000000)
    (
    cond (Nat.beq m 4)
    (591373726471, 1000000000000)
    (
    cond (Nat.beq m 8)
    (141689829501, 250000000000)
    (
    cond (Nat.beq m 16)
    (923009733, 1707106781)
    (
    cond (Nat.beq m 32)
    (898435153, 1707106781)
    (
    cond (Nat.beq m 64)
    (887112193, 1707106781)
    (
    cond (Nat.beq m 128)
    (882583166, 1707106781)
    (
    cond (Nat.beq m 256)
    (877613017, 1707106781)
    (
    cond (Nat.beq m 512)
    (873773349, 1707106781)
    (
    cond (Nat.beq m 1024)
    (873464631, 1707106781)
    (0, 0))))))))))

def altSumNat : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.add x (altSumNat xs)

def muxHitValSum27 : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | p :: ps, vh :: vhs =>
    let rest := muxHitValSum27 ps vhs
    cond (Nat.beq p 0) rest (Nat.add (Nat.mul p vh) rest)

def rkm128kMask56 (rem : ℕ) (words : List ℕ) : List Bool :=
  match rem with
  | 0 => []
  | _ + 1 =>
    match words with
    | [] => []
    | w :: ws =>
      cond (Nat.ble rem 56)
        (rkm128kWordBits rem w)
        (rkm128kWordBits 56 w ++ rkm128kMask56 (Nat.sub rem 56) ws)

def rkm128kSegListLen (segs : List Rkm128kSeg) : ℕ :=
  match segs with
  | [] => 0
  | _ :: rest => Nat.add 1 (rkm128kSegListLen rest)

structure RampKick128kAnchor where
  /-- Active rung `r` (`2 <= r <= kMax`). -/
  rAct : ℕ
  /-- Ordered segment list (`1 <= segs.length <= 128`). -/
  segs : List Rkm128kSeg
  /-- Certified `10 ^ 12`-scaled hit-probability lower bounds `[pLo(1),..., pLo(dEnd)]`. -/
  rowLo12 : List ℕ

def rkm128kLastL (defVal : ℕ) (segs : List Rkm128kSeg) : ℕ :=
  match segs with
  | [] => defVal
  | s :: rest => rkm128kLastL s.lS rest

def rkm128kWeightedTau9 (segs : List Rkm128kSeg) : ℕ :=
  match segs with
  | [] => 0
  | s :: rest => Nat.add (Nat.mul s.lS s.tau9) (rkm128kWeightedTau9 rest)

def rkm128kCheckSegBounds (lTableMax : ℕ) (segs : List Rkm128kSeg) (lPrev : ℕ) : Bool :=
  match segs with
  | [] => true
  | s :: rest =>
    cond
      (Bool.or (primNatBlt s.lS 1)
      (Bool.or (primNatBlt s.lS lPrev)
      (Bool.or (primNatBlt lTableMax s.lS)
      (Bool.or (primNatBlt s.tau9 1)
        (primNatBlt 4000000000 s.tau9)))))
      false
      (rkm128kCheckSegBounds lTableMax rest s.lS)

def rkm128kCheckSegsLMax (lMaxCell : ℕ) (segs : List Rkm128kSeg) : Bool :=
  match segs with
  | [] => true
  | s :: rest =>
    cond (Bool.or (primNatBlt s.lS 1) (primNatBlt lMaxCell s.lS))
      false
      (rkm128kCheckSegsLMax lMaxCell rest)

def rkm128kCeilDiv15 (n : ℕ) : ℕ :=
  Nat.div (Nat.add 999999999999999 n) wdScale

def altPadRightInts : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | rem + 1, xs =>
    match xs with
    | [] => highdStrictConsInt (Int.ofNat 0) (altPadRightInts rem [])
    | x :: rest => highdStrictConsInt x (altPadRightInts rem rest)

def rkm128kVecL1 (xs : List ℤ) : ℕ :=
  match xs with
  | [] => 0
  | x :: rest => Nat.add (primIntNatAbs x) (rkm128kVecL1 rest)

def altNewtonLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | fuel + 1, target, x =>
    let yRaw := Nat.div (Nat.add x (Nat.div target x)) 2
    AltForce.withForcedNat yRaw fun y =>
      cond (Nat.ble x y) x (altNewtonLoop fuel target y)

def rkm128kVecTailToLo12 (totalPad15 : ℕ) (zs : List ℤ) : List ℕ :=
  match zs with
  | [] => []
  | z :: rest =>
    let aLoRaw := Nat.sub (primIntNatAbs z) totalPad15
    AltForce.withForcedNat aLoRaw fun aLo =>
      let pLo15 := Nat.div (Nat.mul aLo aLo) wdScale
      let pLo12 := Nat.div pLo15 1000
      strictNatCons pLo12 (rkm128kVecTailToLo12 totalPad15 rest)

def muxRawIntTdivNat (x : ℤ) (dNat : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => Int.ofNat (Nat.div m dNat)
  | Int.negSucc m => muxRawNegOfNat (Nat.div (Nat.add m 1) dNat)

def muxRawIntMul : ℤ → ℤ → ℤ
  | Int.ofNat m, Int.ofNat n => Int.ofNat (Nat.mul m n)
  | Int.ofNat m, Int.negSucc n => muxRawNegOfNat (Nat.mul m (Nat.add n 1))
  | Int.negSucc m, Int.ofNat n => muxRawNegOfNat (Nat.mul (Nat.add m 1) n)
  | Int.negSucc m, Int.negSucc n => Int.ofNat (Nat.mul (Nat.add m 1) (Nat.add n 1))

def muxRawIntNeg : ℤ → ℤ
  | Int.ofNat n => muxRawNegOfNat n
  | Int.negSucc n => primOfNatForced (Nat.add n 1)

def muxRawIntAdd : ℤ → ℤ → ℤ
  | Int.ofNat m, Int.ofNat n => primOfNatForced (Nat.add m n)
  | Int.ofNat m, Int.negSucc n => muxRawSubNatNat m (Nat.add n 1)
  | Int.negSucc m, Int.ofNat n => muxRawSubNatNat n (Nat.add m 1)
  | Int.negSucc m, Int.negSucc n => primNegSuccForced (Nat.add (Nat.add m n) 1)

def primNegOfNat (x : ℕ) : ℤ :=
  match x with
  | 0 => Int.ofNat 0
  | k + 1 => primNegSuccForced k

def rkm128kCheckDrift (m lTableMax r : ℕ) (segs : List Rkm128kSeg)
    (vR vCapR : ℕ) (rowLo12 vHist : List ℕ) : Bool :=
  let nSegs := rkm128kSegListLen segs
  cond
    (Bool.or (primNatBlt nSegs 1)
    (Bool.or (primNatBlt 128 nSegs)
    (Bool.or (primNatBlt vCapR vR)
      (Bool.not (rkm128kCheckSegBounds lTableMax segs 1)))))
    false
    (let lEnd := rkm128kLastL 0 segs
     let dEnd := highdNatMin (Nat.mul lEnd m) r
     let tot12 := altSumNat rowLo12
     cond
       (Bool.or (Bool.not (Nat.beq (altListLen rowLo12) dEnd))
       (Bool.or (primNatBlt tot12 1)
       (Bool.or (primNatBlt 1000000000000 tot12)
         (primNatBlt (altListLen vHist) dEnd))))
       false
       (let wTau9 := rkm128kWeightedTau9 segs
        let hit27 := muxHitValSum27 rowLo12 vHist
        let def12 := Nat.sub 1000000000000 tot12
        let lhs27 := Nat.add (Nat.mul wTau9 (Nat.mul 1000 wdScale))
          (Nat.add hit27 (Nat.mul def12 vCapR))
        primNatBlt lhs27 (Nat.mul 1000000000000 vR)))

def rkm128kCheckAnchorsLMax (k lMaxCell : ℕ) (anchors : List RampKick128kAnchor) : Bool :=
  match anchors with
  | [] => true
  | a :: rest =>
    let ok := cond (Nat.ble a.rAct k) (rkm128kCheckSegsLMax lMaxCell a.segs) true
    cond ok (rkm128kCheckAnchorsLMax k lMaxCell rest) false

def altIsqrt15 (val : ℕ) : ℕ × ℕ :=
  bif Nat.beq val 0 then (0, 0)
  else
    let targetRaw := Nat.mul val (Nat.mul wdScale wdScale)
    AltForce.withForcedNat targetRaw fun target =>
      let xRaw := altNewtonLoop 20 target (altInitGuess val)
      AltForce.withForcedNat xRaw fun x =>
        let xSq := Nat.mul x x
        AltForce.withForcedNat xSq fun x2 =>
          let x1 := Nat.add x 1
          cond (Bool.and (Nat.ble x2 target) (primNatBlt target (Nat.mul x1 x1)))
            (x, cond (Nat.beq x2 target) x x1)
            (0, Nat.mul val wdScale)

def rkm128kFinalizeState (st : ℕ × ℕ × ℕ × List ℤ) : List ℕ :=
  match st with
  | (lOut, dEnd, accPad, vecFinal) =>
    cond (Bool.or (Nat.beq lOut 0) (Bool.or (Nat.beq dEnd 0) (Nat.beq accPad 0)))
      []
      (let padded := altPadRightInts (Nat.add dEnd 1) vecFinal
       match padded with
       | [] => []
       | _ :: tail => rkm128kVecTailToLo12 accPad tail)

def rkmApplyMaskBits : List Bool → List ℤ → List ℤ
  | _, [] => []
  | [], vs => vs
  | b :: bs, v :: vs =>
    let vNext := cond b (muxRawIntNeg v) v
    highdStrictConsInt vNext (rkmApplyMaskBits bs vs)

def muxRawIntSub (a b : ℤ) : ℤ :=
  muxRawIntAdd a (muxRawIntNeg b)

def rkm128kVecAdd (xs ys : List ℤ) : List ℤ :=
  match xs with
  | [] => ys
  | x :: xRest =>
    match ys with
    | [] => xs
    | y :: yRest =>
      highdStrictConsInt (muxRawIntAdd x y) (rkm128kVecAdd xRest yRest)

def primIntMul : ℤ → ℤ → ℤ
  | Int.ofNat m, Int.ofNat n => primOfNatForced (Nat.mul m n)
  | Int.ofNat m, Int.negSucc n => primNegOfNat (Nat.mul m (Nat.add n 1))
  | Int.negSucc m, Int.ofNat n => primNegOfNat (Nat.mul (Nat.add m 1) n)
  | Int.negSucc m, Int.negSucc n =>
    primOfNatForced (Nat.mul (Nat.add m 1) (Nat.add n 1))

def altCheckHbTightAux (m r : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | rem + 1, w =>
    let rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    let p := altIsqrt15 rad
    cond (Nat.ble p.2 (Nat.add p.1 1)) (altCheckHbTightAux m r rem (Nat.add w 1)) false

def altMaxBHiFromAux (m r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | rem + 1, w =>
    let rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    let bHi := (altIsqrt15 rad).2
    let rest := altMaxBHiFromAux m r rem (Nat.add w 1)
    HighDForce.withForcedNat rest fun rMax =>
      cond (primNatBlt rMax bHi) bHi rMax

def altBuildHbFromAux (m r hPt : ℕ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | rem + 1, w =>
    let rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    let sq := (altIsqrt15 rad).1
    let bNat := Nat.div (Nat.mul hPt sq) wdScale
    strictConsInt (Int.ofNat bNat) (altBuildHbFromAux m r hPt rem (Nat.add w 1))

def checkEigStep (m r vR vPrev : ℕ) : Bool :=
  cond (Bool.or (primNatBlt r 1) (Nat.ble vR vPrev)) false
    (let sqLo := (altIsqrt15 (Nat.mul m r)).1
    cond (Nat.beq sqLo 0) false
      (primNatBlt (Nat.mul 1285398163397449 wdScale)
        (Nat.mul 2 (Nat.mul (Nat.sub vR vPrev) sqLo))))

def rkmCheckColdR2Step (m v2 : ℕ) : Bool :=
  let nd := rkmColdR2NumDen m
  cond (Nat.beq nd.2 0)
    false
    (
    let sqLo := (altIsqrt15 m).1
    cond (Nat.beq sqLo 0)
      false
      (
      let lhs := Nat.mul (Nat.add (Nat.mul nd.1 1707106781186548) (Nat.mul nd.2 1000000))
        785398163397449
      let rhs := Nat.mul (Nat.mul v2 nd.2) sqLo
      primNatBlt lhs rhs))

def harmSumLo15 : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let hi := (altIsqrt15 (Nat.add k 1)).2
    Nat.add (harmSumLo15 k) (Nat.div (Nat.mul wdScale wdScale) hi)

def muxFastSlideLoopAux (dNat : ℕ) : ℕ → ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | 0, _, _, _, _ => []
  | rem + 1, prev, hb, vec, cur =>
    match hb with
    | b :: hbRest =>
      match vec with
      | v :: vTail =>
        match cur with
        | c0 :: cTail =>
          let c1 := match cTail with | cn :: _ => cn | [] => Int.ofNat 0
          let q := muxRawIntTdivNat (muxRawIntSub prev (muxRawIntMul b c1)) dNat
          highdStrictConsInt (muxRawIntAdd v q)
            (muxFastSlideLoopAux dNat rem (primIntMul b c0) hbRest vTail cTail)
        | [] =>
          let q := muxRawIntTdivNat (muxRawIntSub prev (muxRawIntMul b (Int.ofNat 0))) dNat
          highdStrictConsInt (muxRawIntAdd v q)
            (muxFastSlideLoopAux dNat rem (primIntMul b (Int.ofNat 0)) hbRest vTail [])
      | [] =>
        match cur with
        | c0 :: cTail =>
          let c1 := match cTail with | cn :: _ => cn | [] => Int.ofNat 0
          let q := muxRawIntTdivNat (muxRawIntSub prev (muxRawIntMul b c1)) dNat
          highdStrictConsInt (muxRawIntAdd (Int.ofNat 0) q)
            (muxFastSlideLoopAux dNat rem (primIntMul b c0) hbRest [] cTail)
        | [] =>
          let q := muxRawIntTdivNat (muxRawIntSub prev (muxRawIntMul b (Int.ofNat 0))) dNat
          highdStrictConsInt (muxRawIntAdd (Int.ofNat 0) q)
            (muxFastSlideLoopAux dNat rem (primIntMul b (Int.ofNat 0)) hbRest [] [])
    | [] =>
      let vHead := match vec with | v :: _ => v | [] => Int.ofNat 0
      let vTail := match vec with | _ :: vt => vt | [] => []
      let cTail := match cur with | _ :: ct => ct | [] => []
      highdStrictConsInt (muxRawIntAdd vHead (muxRawIntTdivNat prev dNat))
        (muxFastSlideLoopAux dNat rem (Int.ofNat 0) [] vTail cTail)

def rkm128kMatVecL1Loop (prev : ℤ) (hb cur : List ℤ) : ℕ :=
  match cur with
  | [] => primIntNatAbs prev
  | c0 :: cTail =>
    match hb with
    | [] => primIntNatAbs prev
    | b :: hbRest =>
      let c1 :=
        match cTail with
        | cn :: _ => cn
        | [] => Int.ofNat 0
      let entry := muxRawIntSub prev (muxRawIntMul b c1)
      Nat.add (primIntNatAbs entry) (rkm128kMatVecL1Loop (primIntMul b c0) hbRest cTail)

def altCheckHbTight (m r w rem : ℕ) : Bool :=
  altCheckHbTightAux m r rem w

def altMaxBHiFrom (m r w rem : ℕ) : ℕ := altMaxBHiFromAux m r rem w

def altBuildHbFrom (m r hPt w rem : ℕ) : List ℤ :=
  altBuildHbFromAux m r hPt rem w

def rkm128kCheckTableAux (m lTableMax : ℕ) (useColdR2 : Bool)
    (vRem : List ℕ) (r vCapPrev : ℕ) (vHist : List ℕ)
    (anchors : List RampKick128kAnchor) : Bool :=
  match vRem with
  | [] =>
    match anchors with
    | [] => true
    | _ :: _ => false
  | vR :: vRest =>
    match vHist with
    | [] => false
    | vPrev :: _ =>
      let vCapR := cond (primNatBlt vCapPrev vR) vR vCapPrev
      HighDForce.withForcedNat vCapR fun vCapNext =>
        let fallbackOk :=
          cond (Bool.and (Nat.beq r 2) useColdR2)
            (rkmCheckColdR2Step m vR)
            (checkEigStep m r vR vPrev)
        match anchors with
        | a :: aRest =>
          cond (primNatBlt a.rAct r)
            false
            (cond (Nat.beq a.rAct r)
              (cond (rkm128kCheckDrift m lTableMax r a.segs vR vCapNext a.rowLo12 vHist)
                (rkm128kCheckTableAux m lTableMax useColdR2 vRest (Nat.add r 1) vCapNext
                  (vR :: vHist) aRest)
                false)
              (cond fallbackOk
                (rkm128kCheckTableAux m lTableMax useColdR2 vRest (Nat.add r 1) vCapNext
                  (vR :: vHist) (a :: aRest))
                false))
        | [] =>
          cond fallbackOk
            (rkm128kCheckTableAux m lTableMax useColdR2 vRest (Nat.add r 1) vCapNext
              (vR :: vHist) [])
            false

def checkAltBound12 (m k vAtK num den : ℕ) : Bool :=
  cond (Nat.beq den 0) false
    (let sqrtMHi15 := (altIsqrt15 m).2
    let hLo15 := harmSumLo15 k
    Nat.ble (Nat.mul (Nat.mul vAtK sqrtMHi15) den)
      (Nat.mul (Nat.mul num 785398163397448) hLo15))

def muxFastHornerStage (deg maxLen : ℕ) (hb vec cur : List ℤ) : List ℤ :=
  let nxtRaw := highdNatMin maxLen (Nat.add (altIntLen cur) 1)
  HighDForce.withForcedNat nxtRaw fun nxtLen =>
    let dRaw := Nat.mul deg wdScale
    HighDForce.withForcedNat dRaw fun dNat =>
      muxFastSlideLoopAux dNat nxtLen (Int.ofNat 0) hb vec cur

def rkm128kCheckTable (m kMax lTableMax : ℕ) (useColdR2 : Bool)
    (vPot : List ℕ) (anchors : List RampKick128kAnchor) : Bool :=
  cond
    (Bool.or (primNatBlt m 1)
    (Bool.or (primNatBlt lTableMax 1)
    (Bool.or (primNatBlt 8192 (Nat.mul lTableMax m))
    (Bool.or (primNatBlt kMax 2)
    (Bool.or (primNatBlt 1024 kMax)
      (Bool.not (Nat.beq (altListLen vPot) (Nat.add kMax 1))))))))
    false
    (match vPot with
     | v0 :: v1 :: vRest =>
       cond (Bool.not (Nat.beq v0 0))
         false
         (cond (checkEigStep m 1 v1 v0)
           (rkm128kCheckTableAux m lTableMax useColdR2 vRest 2 v1 [v1, v0] anchors)
           false)
     | _ => false)

def rkm128kTaylorLoop (maxLen : ℕ) (hb : List ℤ)
    (rem kIdx : ℕ) (cur acc : List ℤ) (sumZL1 : ℕ) : List ℤ × List ℤ × ℕ :=
  match rem with
  | 0 => (cur, acc, sumZL1)
  | rem' + 1 =>
    let nxtRaw := muxFastHornerStage kIdx maxLen hb [] cur
    HighDForce.withForcedList nxtRaw fun nxt =>
      let accRaw := rkm128kVecAdd acc nxt
      HighDForce.withForcedList accRaw fun accNext =>
        let l1Raw := Nat.add sumZL1 (rkm128kVecL1 nxt)
        HighDForce.withForcedNat l1Raw fun sumNext =>
          rkm128kTaylorLoop maxLen hb rem' (Nat.add kIdx 1) nxt accNext sumNext

def rkm128kSubstep (d bCapCeil degP : ℕ) (hb vec : List ℤ) (accPad : ℕ) : List ℤ × ℕ :=
  cond (Nat.beq accPad 0)
    ([], 0)
    (let l1Init := rkm128kVecL1 vec
     HighDForce.withForcedNat l1Init fun sum0 =>
       match rkm128kTaylorLoop (Nat.add d 1) hb degP 1 vec vec sum0 with
       | (zLast, accEnd, sumZAll) =>
         cond (primNatBlt (Nat.mul 1000 wdScale) sumZAll)
           ([], 0)
           (let remTail := rkm128kCeilDiv15 (rkm128kMatVecL1Loop (Int.ofNat 0) hb zLast)
            let discPad := rkm128kCeilDiv15 (Nat.mul (Nat.add bCapCeil 10) sumZAll)
            let roundPad := Nat.mul 33 degP
            let stepPad := Nat.add remTail (Nat.add discPad (Nat.add roundPad 1))
            let nextPad := Nat.add accPad stepPad
            cond (primNatBlt 100000000000000 nextPad)
              ([], 0)
              (accEnd, nextPad)))

def rkm128kSubstepLoop (remSub d bCapCeil degP : ℕ)
    (hb vec : List ℤ) (accPad : ℕ) : List ℤ × ℕ :=
  match remSub with
  | 0 => (vec, accPad)
  | s + 1 =>
    match rkm128kSubstep d bCapCeil degP hb vec accPad with
    | (v1, p1) =>
      HighDForce.withForcedList v1 fun vForced =>
        HighDForce.withForcedNat p1 fun pForced =>
          rkm128kSubstepLoop s d bCapCeil degP hb vForced pForced

def rkm128kRunOneSeg (m lTableMax r : ℕ) (seg : Rkm128kSeg)
    (lPrev _dCur accPad : ℕ) (vec : List ℤ) : ℕ × ℕ × ℕ × List ℤ :=
  cond (Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0))
    (0, 0, 0, [])
    (let lS := seg.lS
     let tau9 := seg.tau9
     let nSub := seg.nSub
     let degP := seg.degP
     let mask := seg.mask
     let mEff := Nat.mul lS m
     let d := highdNatMin mEff r
     cond
       (Bool.or (primNatBlt lS lPrev)
       (Bool.or (primNatBlt lTableMax lS)
       (Bool.or (primNatBlt mEff 1)
       (Bool.or (primNatBlt 8192 mEff)
       (Bool.or (primNatBlt d 1)
       (Bool.or (Nat.beq tau9 0)
       (Bool.or (primNatBlt 4000000000 tau9)
       (Bool.or (Nat.beq nSub 0)
       (Bool.or (primNatBlt 16384 nSub)
       (Bool.or (Nat.beq degP 0)
       (Bool.or (primNatBlt 64 degP)
         (primNatBlt (Nat.add d 1) (rkmBoolListLen mask)))))))))))))
       (0, 0, 0, [])
       (let hPtRaw := Nat.div (Nat.mul tau9 1000000) nSub
        HighDForce.withForcedNat hPtRaw fun hPt =>
          cond (Bool.or (primNatBlt hPt 1) (Bool.not (altCheckHbTight mEff r 0 d)))
            (0, 0, 0, [])
            (let maxBRaw := altMaxBHiFrom mEff r 0 d
             HighDForce.withForcedNat maxBRaw fun maxBHi15 =>
               let bCapHi15 := Nat.mul 2 maxBHi15
               let bCapCeil := rkm128kCeilDiv15 bCapHi15
               let hbRaw := altBuildHbFrom mEff r hPt 0 d
               HighDForce.withForcedList hbRaw fun hbPt =>
                 let padIn := Nat.add accPad 2
                 match rkm128kSubstepLoop nSub d bCapCeil degP hbPt vec padIn with
                 | (vWalk, padWalk) =>
                   cond (Bool.or (Nat.beq padWalk 0) (primNatBlt 100000000000000 padWalk))
                     (0, 0, 0, [])
                     (let kRaw := rkmApplyMaskBits mask vWalk
                      HighDForce.withForcedList kRaw fun vNext =>
                        (lS, d, padWalk, vNext)))))

def rkm128kRunSegs (m lTableMax r : ℕ) (segs : List Rkm128kSeg)
    (lPrev dCur accPad : ℕ) (vec : List ℤ) : ℕ × ℕ × ℕ × List ℤ :=
  cond (Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0))
    (0, 0, 0, [])
    (match segs with
     | [] => (lPrev, dCur, accPad, vec)
     | seg :: rest =>
       match rkm128kRunOneSeg m lTableMax r seg lPrev dCur accPad vec with
       | (l1, d1, p1, v1) =>
         HighDForce.withForcedNat l1 fun lF =>
           HighDForce.withForcedNat d1 fun dF =>
             HighDForce.withForcedNat p1 fun pF =>
               HighDForce.withForcedList v1 fun vF =>
                 rkm128kRunSegs m lTableMax r rest lF dF pF vF)

def rkm128kEvalRowLo12 (m lTableMax r : ℕ) (segs : List Rkm128kSeg) : List ℕ :=
  let nSegs := rkm128kSegListLen segs
  cond
    (Bool.or (Nat.beq nSegs 0)
    (Bool.or (primNatBlt 128 nSegs)
    (Bool.or (primNatBlt r 2) (primNatBlt 1024 r))))
    []
    (rkm128kFinalizeState (rkm128kRunSegs m lTableMax r segs 1 0 1 [Int.ofNat wdScale]))

def RampKick128kAnchorsSound (m lTableMax : ℕ) (anchors : List RampKick128kAnchor) : Prop :=
  match anchors with
  | [] => True
  | a :: rest =>
    rkm128kEvalRowLo12 m lTableMax a.rAct a.segs = a.rowLo12 ∧
      RampKick128kAnchorsSound m lTableMax rest

end
end QuantumComputation.Specs.DickeSol
