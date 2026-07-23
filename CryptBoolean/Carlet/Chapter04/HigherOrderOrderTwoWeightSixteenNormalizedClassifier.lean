/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenNormalizedCandidates
public meta import Std.Tactic.BVDecide.Reflect

/-!
# Kernel-checked normalized rank-seven pattern classification

The affine-basis normalization of a rank-seven weight-sixteen support is a
128-bit set containing zero and the seven standard basis points.  Self-duality
is exactly the evenness of its seven linear and twenty-one quadratic coordinate
moments.  This file packages the finite classifier that identifies every such
normalized set with an affine image of one of the three canonical patterns.
-/

@[expose] public section

namespace CryptBoolean

set_option linter.style.setOption false in
/-- Run one finite weight-sixteen certificate with its required local
elaboration budget. -/
macro "weightSixteenFiniteCertificate" : tactic =>
  `(tactic| set_option maxHeartbeats 20000000 in bv_decide)

/-- Coordinate support masks on the low half of the seven-variable cube. -/
def normalizedCoordinateMaskLow : Fin 7 → BitVec 64
  | 0 => 0xAAAAAAAAAAAAAAAA#64
  | 1 => 0xCCCCCCCCCCCCCCCC#64
  | 2 => 0xF0F0F0F0F0F0F0F0#64
  | 3 => 0xFF00FF00FF00FF00#64
  | 4 => 0xFFFF0000FFFF0000#64
  | 5 => 0xFFFFFFFF00000000#64
  | 6 => 0#64

/-- Coordinate support masks on the high half of the seven-variable cube. -/
def normalizedCoordinateMaskHigh : Fin 7 → BitVec 64
  | 0 => 0xAAAAAAAAAAAAAAAA#64
  | 1 => 0xCCCCCCCCCCCCCCCC#64
  | 2 => 0xF0F0F0F0F0F0F0F0#64
  | 3 => 0xFF00FF00FF00FF00#64
  | 4 => 0xFFFF0000FFFF0000#64
  | 5 => 0xFFFFFFFF00000000#64
  | 6 => 0xFFFFFFFFFFFFFFFF#64

/-- Whether a 64-bit intersection has even cardinality. -/
def normalizedMaskEven (x : BitVec 64) : Bool :=
  !(x.cpop.getLsbD 0)

/-- The card-sixteen, affine-basis, and degree-at-most-two parity constraints
on a normalized pair of 64-bit support masks. -/
def IsNormalizedWeightSixteenMask (low high : BitVec 64) : Bool :=
  low.cpop + high.cpop == 16#64 &&
    low &&& 0x0000000100010117#64 == 0x0000000100010117#64 &&
    high &&& 1#64 == 1#64 &&
    (List.ofFn fun i : Fin 7 ↦
      normalizedMaskEven (low &&& normalizedCoordinateMaskLow i) ==
        normalizedMaskEven (high &&& normalizedCoordinateMaskHigh i)).all id &&
    (List.ofFn fun i : Fin 7 ↦
      (List.ofFn fun j : Fin 7 ↦
        if i < j then
          normalizedMaskEven
              (low &&& normalizedCoordinateMaskLow i &&&
                normalizedCoordinateMaskLow j) ==
            normalizedMaskEven
              (high &&& normalizedCoordinateMaskHigh i &&&
                normalizedCoordinateMaskHigh j)
        else true).all id).all id

/-- The `i`th systematic column packed into a 64-bit code. -/
def systematicWeightSixteenColumn
    (code : BitVec 64) (i : ℕ) : BitVec 8 :=
  code.extractLsb' (8 * i) 8

/-- A systematic column is odd and is not one of the eight unit columns already
occupied by the normalized affine basis. -/
def isSystematicWeightSixteenNonunitOddColumn (column : BitVec 8) : Bool :=
  column.cpop.getLsbD 0 && column &&& (column - 1) != 0

/-- Two systematic columns are orthogonal over the binary field. -/
def areSystematicWeightSixteenColumnsOrthogonal
    (left right : BitVec 8) : Bool :=
  !((left &&& right).cpop.getLsbD 0)

/-- The eight sorted columns form an orthonormal basis and avoid the eight
unit columns already occupied by the normalized affine basis. -/
def SystematicWeightSixteenConstraints (code : BitVec 64) : Bool :=
  isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 0) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 1) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 2) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 3) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 4) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 5) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 6) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 7) &&
    (systematicWeightSixteenColumn code 0).ult
      (systematicWeightSixteenColumn code 1) &&
    (systematicWeightSixteenColumn code 1).ult
      (systematicWeightSixteenColumn code 2) &&
    (systematicWeightSixteenColumn code 2).ult
      (systematicWeightSixteenColumn code 3) &&
    (systematicWeightSixteenColumn code 3).ult
      (systematicWeightSixteenColumn code 4) &&
    (systematicWeightSixteenColumn code 4).ult
      (systematicWeightSixteenColumn code 5) &&
    (systematicWeightSixteenColumn code 5).ult
      (systematicWeightSixteenColumn code 6) &&
    (systematicWeightSixteenColumn code 6).ult
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 1) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 2) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 3) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 2) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 3) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 3) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 4)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 4)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 4)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 5)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 5)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 6)
      (systematicWeightSixteenColumn code 7)

/-- The finite family of two-column prefixes that extend to a generated
systematic orthonormal basis. -/
def IsSystematicWeightSixteenPrefixAllowed (code : BitVec 64) : Bool :=
  (
    (
      (
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 2823 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 3335) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 3339 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 3591)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 3595 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 3597) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 4871 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 4875))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 5383 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 5389) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 5395 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 5639)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 5646 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 5651) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 5653 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 6411 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 6413))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 6419 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 6421) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 6667 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 6670)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 6675 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 6678) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 6681 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 7181))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 7182 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 7189) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 7190 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 7193)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 7194 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 8967) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 8971 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 8979 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 8988)))))) ||
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 8991 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9479) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9485 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9493)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9498 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9503) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9507 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9735))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9742 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9750) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9753 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9759)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9763 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 9765) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10507 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 10509 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 10518))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10521 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10527) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10531 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10533)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10763 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10766) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10773 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 10778 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 10783)))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10787 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10790) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 10793 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 11277)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 11278 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 11283) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 11292 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 11295 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 11301))))))) ||
      (
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 11302 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 11305) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 11306 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12051)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12053 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12054) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12057 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12058))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12060 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12063) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12558 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12563)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12565 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12569) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12575 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 12579 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 12581))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12585 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12591) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12813 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12819)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12822 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12826) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12831 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 12835 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 12838)))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12842 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12847) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 12849 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13323)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13333 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13334) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13340 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 13343 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 13349)))))) ||
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13350 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13356) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13359 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13361)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 13362 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14091) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14093 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14094))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14105 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14106) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14108 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14111)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14121 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14122) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14124 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 14127 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 14343))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14361 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14362) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14364 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14367)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14377 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14378) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14380 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 14383 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 14385)))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14386 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14388) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 14391 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15111)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15117 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15118) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15125 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 15126 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 15132)))))))) ||
    (
      (
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15135 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15141) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15142 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15148)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15151 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15156) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15159 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15623))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15627 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15630) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15635 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15638)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15642 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15647) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15651 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 15654 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 15658))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15663 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15666) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15671 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15675)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15879 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15883) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15885 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15891))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15893 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15897) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15903 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15907)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15909 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15913) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15919 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 15921 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 15927)))))) ||
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15931 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 15933) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 17731 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 17987)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 17989 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 18755) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 18757 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 19011))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 19014 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 19017) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 19525 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 19526)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 19529 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 19530) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 20803 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 20805 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 20809))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 20815 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21059) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21062 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21066)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21071 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21073) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21573 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 21574 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 21580)))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21583 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21585) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 21586 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22345)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22346 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22348) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22351 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 22601 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 22602))))))) ||
      (
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22604 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22607) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22609 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22610)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22612 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 22615) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23365 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23366))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23372 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23375) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23380 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23383)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23875 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23878) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23882 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 23887 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 23890))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23895 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 23899) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 24131 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 24133)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 24137 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 24143) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 24145 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 24151 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 24155)))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 24157 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 25185) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 25697 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 25698)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 26721 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 26722) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 26724 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 26727 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 27492)))))) ||
        (
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 27495 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 28002) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 28007 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 28011)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 28257 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 28263) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 28267 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 28269))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 30067 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 30323) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 30325 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 31353)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 33663 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 34175) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 34431 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 35199 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 35455))))) ||
          (
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 35967 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 36735) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 37247 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 37503)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 38015 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 38783) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 39807 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 40319 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 41343)))) ||
            (
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 41599 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 42111) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 42879 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 43903)) ||
              (
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 44415 ||
                  code.extractLsb' 0 16 == BitVec.ofNat 16 45951) ||
                (
                  code.extractLsb' 0 16 == BitVec.ofNat 16 46463 ||
                  (
                    code.extractLsb' 0 16 == BitVec.ofNat 16 47487 ||
                    code.extractLsb' 0 16 == BitVec.ofNat 16 49023)))))))))

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 20000000 in
/-- Every systematic orthonormal-column code has one of the generated
two-column prefixes. -/
theorem systematicWeightSixteen_prefix_allowed (code : BitVec 64)
    (hconstraints : SystematicWeightSixteenConstraints code = true) :
    IsSystematicWeightSixteenPrefixAllowed code = true := by
  unfold SystematicWeightSixteenConstraints systematicWeightSixteenColumn at hconstraints
  unfold isSystematicWeightSixteenNonunitOddColumn at hconstraints
  unfold areSystematicWeightSixteenColumnsOrthogonal at hconstraints
  unfold IsSystematicWeightSixteenPrefixAllowed
  bv_decide

/-- Boolean membership in the generated systematic-code family. -/
def isGeneratedSystematicWeightSixteenCode (code : BitVec 64) : Bool :=
  match normalizedWeightSixteenCandidateBucket (code.extractLsb' 0 16) with
  | some tree => tree.containsSystematicCode code
  | none => false

private theorem exists_candidate_of_tree_containsSystematicCode
    (tree : NormalizedWeightSixteenCandidateTree) (code : BitVec 64)
    (hcontains : tree.containsSystematicCode code = true) :
    ∃ candidate,
      tree.Member candidate ∧ candidate.systematicCode = code := by
  induction tree with
  | leaf candidate =>
      refine ⟨candidate, .leaf, ?_⟩
      simpa [NormalizedWeightSixteenCandidateTree.containsSystematicCode]
        using hcontains
  | node left right ihLeft ihRight =>
      have hcases :
          left.containsSystematicCode code = true ∨
            right.containsSystematicCode code = true := by
        simpa [NormalizedWeightSixteenCandidateTree.containsSystematicCode]
          using hcontains
      rcases hcases with hleft | hright
      · obtain ⟨candidate, hmember, hcode⟩ := ihLeft hleft
        exact ⟨candidate, .left hmember, hcode⟩
      · obtain ⟨candidate, hmember, hcode⟩ := ihRight hright
        exact ⟨candidate, .right hmember, hcode⟩

/-- A successful generated-code test carries an actual class and affine-map
certificate leaf, rather than only a Boolean membership result. -/
theorem exists_normalizedWeightSixteenCandidate_of_generated
    (code : BitVec 64)
    (hgenerated : isGeneratedSystematicWeightSixteenCode code = true) :
    ∃ tree candidate,
      normalizedWeightSixteenCandidateBucket (code.extractLsb' 0 16) =
          some tree ∧
        NormalizedWeightSixteenCandidateTree.Member candidate tree ∧
        candidate.systematicCode = code := by
  unfold isGeneratedSystematicWeightSixteenCode at hgenerated
  split at hgenerated
  next tree heq =>
    obtain ⟨candidate, hmember, hcode⟩ :=
      exists_candidate_of_tree_containsSystematicCode tree code hgenerated
    exact ⟨tree, candidate, heq, hmember, hcode⟩
  next heq => simp at hgenerated

end CryptBoolean
