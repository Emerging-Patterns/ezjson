# For texts shorter than 2^32 - 1 characters: inside a string, `\"`, `\\`,
# `\/`, `\b`, `\f`, `\n`, `\r`, `\t` decode to their characters; `\uXXXX` of a
# non-surrogate decodes to that code point; a high then low surrogate escape
# decodes to one code point; any other escape, and an unpaired surrogate
# escape, make `parse` `None` (§7, §8.2)
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1
import ./defs/GrammarDerivations.bend as D2

# whether a text starts with nn hexadecimal digits
def hexn(nn: Nat, cs: List<&2, Char>) -> Bool:
  match nn:
    case 0n:
      True{}
    case 1n+p:
      match cs:
        case Nil{}:
          False{}
        case hd <> tl:
          Bool.and(D2.hexd(hd), hexn(p, tl))

# whether a text starts with nn + 1 more hexadecimal digits that, added in
# base 16 to acc, spell a low surrogate
def lo_tail(cs: List<&2, Char>, nn: Nat, acc: U32) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case +hd <> tl:
      match nn:
        case 0n:
          Bool.and(D2.hexd(hd), D2.lo_sur(D2.hex.acc(acc, hd)))
        case 1n+p:
          Bool.and(D2.hexd(hd), lo_tail(tl, p, D2.hex.acc(acc, hd)))

# whether a text starts with u and a low surrogate's four hexadecimal digits
def lo_next.u(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case hd <> tl:
      Bool.and(D1.is_cp(hd, 117), lo_tail(tl, 3n, 0))

# whether a text starts with a low surrogate's \u escape
def lo_next(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case hd <> tl:
      Bool.and(D1.is_cp(hd, 92), lo_next.u(tl))

# LAW: inside a string, a two-character escape decodes to its character
law esc_decodes:
  for +pre: String
  for +ch: Char
  for +cc: Char
  for +post: String
  for h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_e: {D2.unesc(ch) == Some{cc} : Maybe<&2, Char>}
  for h_q: {D1.raw_ok(String.to_list(post)) == True{} : Bool}
  for h_s: {D1.short("\"" ++ pre ++ SCon{'\\', SCon{ch, post}} ++ "\"") == True{} : Bool}
  {D1.str_of(Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{ch, post}} ++ "\"")) == Some{pre ++ SCon{cc, post}} :
    Maybe<&2, String>}

# LAW: inside a string, a backslash before any character but those of a
# two-character escape or u makes parse None, whatever follows
law esc_bad:
  for +pre: String
  for +ch: Char
  for +rest: String
  for h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_e: {D2.unesc(ch) == None{} : Maybe<&2, Char>}
  for h_u: {D1.is_cp(ch, 117) == False{} : Bool}
  for h_s: {D1.short("\"" ++ pre ++ SCon{'\\', SCon{ch, rest}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{ch, rest}}) == None{} : Maybe<&2, V.Json>}

# LAW: inside a string, \u and four hexadecimal digits of a code point that
# is no surrogate decode to that code point
law esc_u:
  for +pre: String
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +post: String
  for h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_h: {Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc), D2.hexd(dd)))) == True{} : Bool}
  for h_n: {D2.non_sur(D2.hex4(aa, bb, cc, dd)) == True{} : Bool}
  for h_q: {D1.raw_ok(String.to_list(post)) == True{} : Bool}
  for h_s: {D1.short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
    post}}}}}} ++ "\"") == True{} : Bool}
  {D1.str_of(Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
      post}}}}}} ++ "\"")) ==
    Some{pre ++ SCon{Char.from_u32(D2.hex4(aa, bb, cc, dd)), post}} : Maybe<&2, String>}

# LAW: inside a string, a high then a low surrogate escape decode to the one
# code point they stand for
law esc_pair:
  for +pre: String
  for +h1: Char
  for +h2: Char
  for +h3: Char
  for +h4: Char
  for +l1: Char
  for +l2: Char
  for +l3: Char
  for +l4: Char
  for +post: String
  for h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_h: {Bool.and(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3), D2.hexd(h4)))) == True{} : Bool}
  for h_l: {Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))) == True{} : Bool}
  for h_hi: {D2.in_hi(D2.hex4(h1, h2, h3, h4)) == True{} : Bool}
  for h_lo: {D2.lo_sur(D2.hex4(l1, l2, l3, l4)) == True{} : Bool}
  for h_q: {D1.raw_ok(String.to_list(post)) == True{} : Bool}
  for h_s: {D1.short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
      SCon{l1,
    SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\"") == True{} : Bool}
  {D1.str_of(Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
    SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\"")) ==
    Some{pre ++ SCon{Char.from_u32(D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))), post}} : Maybe<&2,
        String>}

# LAW: inside a string, \u not followed by four hexadecimal digits makes
# parse None, whatever follows
law esc_u_bad:
  for +pre: String
  for +rest: String
  for h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_x: {hexn(4n, String.to_list(rest)) == False{} : Bool}
  for h_s: {D1.short("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}) == None{} : Maybe<&2, V.Json>}

# LAW: inside a string, a low surrogate escape with no high one before it
# makes parse None, whatever follows
law esc_lo_bad:
  for +pre: String
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +rest: String
  for h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_h: {Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc), D2.hexd(dd)))) == True{} : Bool}
  for h_lo: {D2.lo_sur(D2.hex4(aa, bb, cc, dd)) == True{} : Bool}
  for h_s: {D1.short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
      rest}}}}}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}) == None{} :
    Maybe<&2, V.Json>}

# LAW: inside a string, a high surrogate escape not followed by a low
# surrogate escape makes parse None
law esc_hi_bad:
  for +pre: String
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +rest: String
  for h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_h: {Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc), D2.hexd(dd)))) == True{} : Bool}
  for h_hi: {D2.in_hi(D2.hex4(aa, bb, cc, dd)) == True{} : Bool}
  for h_n: {lo_next(String.to_list(rest)) == False{} : Bool}
  for h_s: {D1.short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
      rest}}}}}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}) == None{} :
    Maybe<&2, V.Json>}
