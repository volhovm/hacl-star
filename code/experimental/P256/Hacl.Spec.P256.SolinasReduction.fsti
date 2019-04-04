module Hacl.Spec.P256.SolinasReduction

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
module D = Hacl.Spec.Curve25519.Field64.Definition
module C =  Hacl.Spec.Curve25519.Field64.Core
open FStar.Mul
open Lib.Sequence

open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Definitions

val solinas_reduction: f: felem8 -> Tot (r: felem4 {D.as_nat4 r = (D.wide_as_nat4 f) % prime})