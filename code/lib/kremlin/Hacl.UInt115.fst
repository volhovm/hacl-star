module Hacl.UInt115
(* This module generated automatically using [mk_int.sh] *)

open FStar.UInt64

open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [Hacl.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

let n = 115

let lemma_value_pow2_115 (x:nat) : Lemma (requires (x = 115)) (ensures (pow2 x = 0x80000000000000000000000000000)) = assert_norm(pow2 115 = 0x80000000000000000000000000000)

let uint64_t = t

type t = | UInt115: high:uint64_t -> low:uint64_t -> t
// type t = {
//   high:uint64_t;
//   low:uint64_t;
//   }

inline_for_extraction
let v (x:t) : GTot (FStar.UInt.uint_t n) =
  0x10000000000000000 * v x.high + v x.low

let add (x:t) (y:t) = UInt115 (x.high +^ y.high) (x.low +^ y.low)

(* Bitwise operators *)
inline_for_extraction let logand (x:t) (y:t) = UInt115 (x.high &^ y.high) (x.low &^ y.low)
inline_for_extraction let logxor (x:t) (y:t) = UInt115 (x.high ^^ y.high) (x.low ^^ y.low)
inline_for_extraction let logor (x:t) (y:t) = UInt115 (x.high |^ y.high) (x.low |^ y.low)
inline_for_extraction let lognot (x:t) = UInt115 (lognot x.high) (lognot x.low)

inline_for_extraction
let mask_26:m:uint64_t{UInt64.v m = pow2 26 - 1} = assert_norm(pow2 26 - 1 = 0x3ffffff); 0x3ffffffuL
inline_for_extraction
let mask_25:m:uint64_t{UInt64.v m = pow2 25 - 1} = assert_norm(pow2 25 - 1 = 0x1ffffff); 0x1ffffffuL
inline_for_extraction
let mask_51:m:uint64_t{UInt64.v m = pow2 51 - 1} = assert_norm(pow2 51 - 1 = 0x7ffffffffffff); 0x7ffffffffffffuL

let mul_wide (x:uint64_t) (y:uint64_t) =
  let mask = mask_26 in
  let x0 = x &^ mask in
  let x1 = x >>^ 26ul in
  let y0 = y &^ mask in
  let y1 = y >>^ 26ul in
  let l  = x0 *^ y0 in
  let m  = (x0 *^ y1) +^ (y0 *^ x1) in
  let h  = x1 *^ y1 in
  UInt115 ((h <<^ 1ul) +^ (m >>^ 25ul)) (l +^ ((m &^ mask_25) <<^ 26ul))

let square (x:uint64_t) =
  let mask = mask_26 in
  // assert_norm(pow2 26 - 1 = UInt64.v mask);
  let x0 = x &^ mask in
  let x1 = x >>^ 26ul in
  let l  = x0 *^ x0 in
  let m  = (x0 *^ x1) <<^ 1ul in
  let h  = x1 *^ x1 in
  UInt115 ((h <<^ 1ul) +^ (m >>^ 25ul)) (l +^ ((m &^ mask_25) <<^ 26ul))

let uint64_to_uint115 (x:uint64_t) =
  UInt115 (x >>^ 51ul) (x &^ mask_51)

let uint115_to_uint64 (x:t) =
  x.low +^ (x.high <<^ 51ul)

let split51_low (s:t) =
  s.low &^ mask_51

let split51_high (s:t) =
  s.high +^ (s.low >>^ 51ul)

let split51_high_full (s:t) =
  UInt115 (s.high >>^ 51ul) ((s.high &^ mask_51) +^ (s.low >>^ 51ul))

// (* Shift operators *)
// inline_for_extraction val shift_right: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))})
// inline_for_extraction let shift_right a s = shift_right a s

// inline_for_extraction val shift_left: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})
// inline_for_extraction let shift_left a s = shift_left a s

// inline_for_extraction val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
// inline_for_extraction let eq_mask a b = eq_mask a b
// inline_for_extraction val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
// inline_for_extraction let gte_mask a b = gte_mask a b
// inline_for_extraction val gt_mask: a:t -> b:t -> Tot (c:t{(v a > v b ==> v c = pow2 n - 1) /\ (v a <= v b ==> v c = 0)})
// inline_for_extraction let gt_mask a b = lognot (gte_mask b a)
// inline_for_extraction val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})
// inline_for_extraction let lt_mask a b = lognot (gte_mask a b)
// inline_for_extraction val lte_mask: a:t -> b:t -> Tot (c:t{(v a <= v b ==> v c = pow2 n - 1) /\ (v a > v b ==> v c = 0)})
// inline_for_extraction let lte_mask a b = lognot (gt_mask a b)


// (* Infix notations *)

// inline_for_extraction val op_Plus_Hat: a:t -> b:t{UInt.size (v a + v b) n} -> Tot (c:t{v a + v b = v c})
// inline_for_extraction let op_Plus_Hat a b = add a b

// inline_for_extraction val op_Plus_Percent_Hat: a:t -> b:t -> Tot (c:t{(v a + v b) % pow2 n = v c})
// inline_for_extraction let op_Plus_Percent_Hat a b = add_mod a b

// inline_for_extraction val op_Subtraction_Hat: a:t -> b:t{(UInt.size (v a - v b) n)} -> Tot (c:t{v a - v b = v c})
// inline_for_extraction let op_Subtraction_Hat a b = sub a b

// inline_for_extraction val op_Subtraction_Percent_Hat: a:t -> b:t -> Tot (c:t{(v a - v b) % pow2 n = v c})
// inline_for_extraction let op_Subtraction_Percent_Hat a b = sub_mod a b

// inline_for_extraction val op_Amp_Hat: t -> t -> Tot t
// inline_for_extraction let op_Amp_Hat a b = logand a b
// inline_for_extraction val op_Hat_Hat: t -> t -> Tot t
// inline_for_extraction let op_Hat_Hat a b = logxor a b
// inline_for_extraction val op_Bar_Hat: t -> t -> Tot t
// inline_for_extraction let op_Bar_Hat a b = logor a b

// (* Shift operators *)
// inline_for_extraction val op_Greater_Greater_Hat: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))})
// inline_for_extraction let op_Greater_Greater_Hat a s = shift_right a s

// inline_for_extraction val op_Less_Less_Hat: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})
// inline_for_extraction let op_Less_Less_Hat a s = shift_left a s

// inline_for_extraction val mul_wide: a:Hacl.UInt64.t -> b:Hacl.UInt64.t -> Tot (c:t{v c = Hacl.UInt64.v a * Hacl.UInt64.v b})
// inline_for_extraction let mul_wide a b = mul_wide a b

// inline_for_extraction val op_Star_Hat: a:Hacl.UInt64.t -> b:Hacl.UInt64.t -> Tot (c:t{v c = Hacl.UInt64.v a * Hacl.UInt64.v b})
// inline_for_extraction let op_Star_Hat a b = mul_wide a b

// (* To input / output constants *)
// assume val of_string: string -> Tot t
