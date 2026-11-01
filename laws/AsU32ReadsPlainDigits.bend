# `as_u32(num(s))` is `Some{n}` exactly when `s` is one or more ASCII digits,
# with no leading zero unless `s` is `0`, whose value `n` is at most
# 4294967295
import Base
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# the value of a text of digits read after acc, in base 10: each digit is
# its code point less 48
def dec_val(+cs: List<&2, Char>, acc: Nat) -> Nat:
  match cs:
    case Nil{}:
      acc
    case ch <> tl:
      dec_val(tl, Nat.add(Nat.mul(acc, 10n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)))

# whether a Nat fits in kk bits, that is, is below 2^kk: halving it kk
# times leaves 0. fits(32n, vv) says vv is at most 4294967295. It is not
# written against the Nat literal 4294967295n because the checker expands a
# Nat literal to that many successors, and 2^32 of them do not fit
def fits(kk: Nat, vv: Nat) -> Bool:
  match kk:
    case 0n:
      Nat.is_eq(vv, 0n)
    case 1n+pp:
      fits(pp, D1.half(vv))

# a Nat when cond holds, else none
def nat_if(cond: Bool, vv: Nat) -> Maybe<&2, Nat>:
  match cond:
    case True{}:
      Some{vv}
    case False{}:
      None{}

# a U32 read as a Nat
def u32_nat(mb: Maybe<&2, U32>) -> Maybe<&2, Nat>:
  match mb:
    case None{}:
      None{}
    case Some{uu}:
      Some{U32.to_nat(uu)}

# what as_u32 of num reads, as a Nat: a decimal's value, when that value is
# at most 4294967295
def dec_u32(+cs: List<&2, Char>) -> Maybe<&2, Nat>:
  nat_if(Bool.and(D1.decimal(cs), fits(32n, dec_val(cs, 0n))), dec_val(cs, 0n))

# LAW: as_u32 of num reads a text exactly when the text is one or more ASCII
# digits, with no leading zero unless it is 0, whose value is at most
# 4294967295, and then it reads a U32 of that value
law as_u32_num:
  for +txt: String
  {u32_nat(Ezjson.as_u32(Ezjson.num(txt))) == dec_u32(String.to_list(txt)) : Maybe<&2, Nat>}

# LAW: a U32 is fixed by its value, so the U32 as_u32_num reads is the one
# with the text's value
law u32_nat_inj:
  for +aa: U32
  for +bb: U32
  for h: {U32.to_nat(aa) == U32.to_nat(bb) : Nat}
  {aa == bb : U32}
