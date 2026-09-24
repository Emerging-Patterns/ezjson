# ezjson: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend ezjson/PROOF.bend`
# is the gate.
import Base
import ./value.bend as V
import ./main.bend as Ezjson
import ./print.bend as Print
import ./pull.bend as Pull

# a boolean
def is_bool(val: V.Json) -> Bool:
  match val:
    case V.JBool{_}:
      True{}
    case _:
      False{}

# a string, owned or a span of the source
def is_str(val: V.Json) -> Bool:
  match val:
    case V.JStr{_}:
      True{}
    case V.JSpan{_, _}:
      True{}
    case _:
      False{}

# a number
def is_num(val: V.Json) -> Bool:
  match val:
    case V.JNum{_}:
      True{}
    case _:
      False{}

# an array
def is_arr(val: V.Json) -> Bool:
  match val:
    case V.JArr{_}:
      True{}
    case _:
      False{}

# an object
def is_obj(val: V.Json) -> Bool:
  match val:
    case V.JObj{_}:
      True{}
    case _:
      False{}

# every value of a list is well-formed
def all_wf(xs: List<&2, V.Json>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case hd <> tl:
      Bool.and(V.wf(hd), all_wf(tl))

# every value of a list of pairs is well-formed
def all_wf_pairs(ps: List<&1, String & V.Json>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case (_, vv) <> tl:
      Bool.and(V.wf(vv), all_wf_pairs(tl))

# a surrogate or a code point past U+10FFFF: not a Unicode scalar value
def non_scalar(+cp: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(cp, 55296), U32.is_le(cp, 57343)), U32.is_gt(cp, 1114111))

# every character of the text is a Unicode scalar value
def scalars(+txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{hd, tl}:
      Bool.and(Bool.not(non_scalar(Char.to_u32(hd))), scalars(tl))

# the characters of a parsed string value; none when parsing failed or gave
# anything else
def str_of(mb: Maybe<&2, V.Json>) -> Maybe<&2, String>:
  match mb:
    case None{}:
      None{}
    case Some{jj}:
      Ezjson.as_str(jj)

# whether a parse result is well-formed: none is, trivially
def wf_m(mb: Maybe<&2, V.Json>) -> Bool:
  match mb:
    case None{}:
      True{}
    case Some{jj}:
      V.wf(jj)

# a value with every span read out into its own string: two values are `same`
# exactly when their owned forms are equal
def own(val: V.Json) -> V.Json:
  match val:
    case V.JNull{}:
      V.JNull{}
    case V.JBool{bb}:
      V.JBool{bb}
    case V.JNum{raw}:
      V.JNum{raw}
    case V.JStr{txt}:
      V.JStr{txt}
    case V.JArr{items}:
      V.JArr{own(items)}
    case V.JObj{pairs}:
      V.JObj{own(pairs)}
    case V.JNil{}:
      V.JNil{}
    case V.JCons{hd, tl}:
      V.JCons{own(hd), own(tl)}
    case V.JPair{kk, vv, rr}:
      V.JPair{kk, own(vv), own(rr)}
    case V.JSpan{src, +nn}:
      V.JStr{V.span.str(src, nn, U32.is_zero(nn))}
    case V.JBind{src, +nn, vv, rr}:
      V.JPair{V.span.str(src, nn, U32.is_zero(nn)), own(vv), own(rr)}

# a parse result, owned
def own_m(mb: Maybe<&2, V.Json>) -> Maybe<&2, V.Json>:
  match mb:
    case None{}:
      None{}
    case Some{jj}:
      Some{own(jj)}

# a character as print writes it: U+FFFD for one that is not a Unicode scalar
# value
def fix_char(+ch: Char) -> Char:
  Bool.pick(Char, non_scalar(Char.to_u32(ch)), Char.from_u32(65533), ch)

# a string as print writes it, character by character
def fix_str(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{hd, tl}:
      SCon{fix_char(hd), fix_str(tl)}

# a value with its strings and keys as print writes them
def fixv(val: V.Json) -> V.Json:
  match val:
    case V.JNull{}:
      V.JNull{}
    case V.JBool{bb}:
      V.JBool{bb}
    case V.JNum{raw}:
      V.JNum{raw}
    case V.JStr{txt}:
      V.JStr{fix_str(txt)}
    case V.JArr{items}:
      V.JArr{fixv(items)}
    case V.JObj{pairs}:
      V.JObj{fixv(pairs)}
    case V.JNil{}:
      V.JNil{}
    case V.JCons{hd, tl}:
      V.JCons{fixv(hd), fixv(tl)}
    case V.JPair{kk, vv, rr}:
      V.JPair{fix_str(kk), fixv(vv), fixv(rr)}
    case V.JSpan{src, nn}:
      V.JSpan{src, nn}
    case V.JBind{src, nn, vv, rr}:
      V.JBind{src, nn, fixv(vv), fixv(rr)}

# a parse result printed; none when parsing failed
def print_m(mb: Maybe<&2, V.Json>) -> Maybe<&2, String>:
  match mb:
    case None{}:
      None{}
    case Some{jj}:
      Some{Ezjson.print(jj)}

# RFC 8259 §6, the grammar a JSON number must match, one def per production:
#
#   number = [ minus ] int [ frac ] [ exp ]
#   int    = zero / ( digit1-9 *DIGIT )
#   frac   = decimal-point 1*DIGIT
#   exp    = e [ minus / plus ] 1*DIGIT
#
# Each def reads what is left of the text and says whether the rest of the
# number, then the end of the text, follows. Alternatives are read in order,
# the first that starts here wins, as a PEG reads ABNF

# `yes` when cond holds, else `no`: one ordered alternative
def when(cond: Bool, yes: Bool, no: Bool) -> Bool:
  match cond:
    case True{}:
      yes
    case False{}:
      no

# the character is the code point
def is_cp(+ch: Char, +cp: U32) -> Bool:
  U32.is_eq(Char.to_u32(ch), cp)

# DIGIT = %x30-39
def digit(+ch: Char) -> Bool:
  Bool.and(U32.is_ge(Char.to_u32(ch), 48), U32.is_le(Char.to_u32(ch), 57))

# digit1-9 = %x31-39
def digit19(+ch: Char) -> Bool:
  Bool.and(U32.is_ge(Char.to_u32(ch), 49), U32.is_le(Char.to_u32(ch), 57))

# e = %x65 / %x45
def is_e(+ch: Char) -> Bool:
  Bool.or(is_cp(ch, 101), is_cp(ch, 69))

# *DIGIT, then the end
def digits_end(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      when(digit(ch), digits_end(tl), False{})

# 1*DIGIT, then the end
def digits1_end(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(digit(ch), digits_end(tl), False{})

# exp after its e: [ minus / plus ] 1*DIGIT, then the end
def exp_body(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(is_cp(ch, 43), digits1_end(tl),
        when(is_cp(ch, 45), digits1_end(tl),
          when(digit(ch), digits_end(tl), False{})))

# the rest of frac's digits, then [ exp ], then the end
def digits_exp_end(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      when(digit(ch), digits_exp_end(tl), when(is_e(ch), exp_body(tl), False{}))

# frac after its decimal point: 1*DIGIT, then [ exp ], then the end
def frac_body(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(digit(ch), digits_exp_end(tl), False{})

# after an int of `0`: no further digit, then [ frac ] [ exp ], then the end
def zero_rest(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      when(digit(ch), False{},
        when(is_cp(ch, 46), frac_body(tl), when(is_e(ch), exp_body(tl), False{})))

# after digit1-9: *DIGIT, then [ frac ] [ exp ], then the end
def digits_rest(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      when(digit(ch), digits_rest(tl),
        when(is_cp(ch, 46), frac_body(tl), when(is_e(ch), exp_body(tl), False{})))

# int [ frac ] [ exp ], then the end
def int_end(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(is_cp(ch, 48), zero_rest(tl), when(digit19(ch), digits_rest(tl), False{}))

# number, then the end
def number(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(is_cp(ch, 45), int_end(tl), int_end(ch <> tl))

# the lowercase hexadecimal digits, in order
def hex_lower() -> String:
  "0123456789abcdef"

# the character at a position of a text; U+0000 past its end
def char_at(+txt: String, left: Nat) -> Char:
  match txt left:
    case SNil{} _:
      Char.from_u32(0)
    case SCon{hd, _} 0n:
      hd
    case SCon{_, tl} 1n+pp:
      char_at(tl, pp)

# the list's value at a position; null past the end
def nth(+xs: List<&2, V.Json>, left: Nat) -> V.Json:
  match xs:
    case Nil{}:
      V.JNull{}
    case hd <> tl:
      match left:
        case 0n:
          hd
        case 1n+pp:
          nth(tl, pp)

# a string, a key, or a number event, span or owned: the events with text
def has_text(ev: Pull.Ev) -> Bool:
  match ev:
    case Pull.EStr{_}:
      True{}
    case Pull.EStrS{_, _}:
      True{}
    case Pull.EKey{_}:
      True{}
    case Pull.EKeyS{_, _}:
      True{}
    case Pull.ENum{_, _}:
      True{}
    case _:
      False{}

# the first `left` characters of a string, or all of it when shorter
def take(+txt: String, left: Nat) -> String:
  match txt:
    case SNil{}:
      ""
    case SCon{hd, tl}:
      match left:
        case 0n:
          ""
        case 1n+pp:
          SCon{hd, take(tl, pp)}

# the event a step of the cursor gave
def ev_of(got: (Pull.Ev & Pull.Cur)) -> Pull.Ev:
  (ev, _cur) = got
  ev

# the cursor a step of the cursor left
def cur_of(got: (Pull.Ev & Pull.Cur)) -> Pull.Cur:
  (_ev, cur) = got
  cur

# the error event
def is_err(ev: Pull.Ev) -> Bool:
  match ev:
    case Pull.EErr{}:
      True{}
    case _:
      False{}

# the end event
def is_end(ev: Pull.Ev) -> Bool:
  match ev:
    case Pull.EEnd{}:
      True{}
    case _:
      False{}

# a cursor that has failed
def failed(cur: Pull.Cur) -> Bool:
  match cur:
    case Pull.Cur{_, _, _, bad}:
      bad

# a cursor with nothing left to read, the root over, and no failure
def ended(cur: Pull.Cur) -> Bool:
  match cur:
    case Pull.Cur{SNil{}, _, True{}, False{}}:
      True{}
    case _:
      False{}

# one of JSON's four whitespace characters (RFC 8259 §2)
def is_ws(+ch: Char) -> Bool:
  Bool.or(is_cp(ch, 32), Bool.or(is_cp(ch, 9), Bool.or(is_cp(ch, 10), is_cp(ch, 13))))

# where a scan of JSON text is: outside strings, inside one, just after a
# backslash inside one, or past whitespace outside strings. RFC 8259 §7: a
# string runs from a quotation mark to the next one no backslash escapes
type Tx is Data:
  TxOut{}
  TxIn{}
  TxEsc{}
  TxWs{}

# one character of the scan
def tx.step(st: Tx, +ch: Char) -> Tx:
  match st:
    case TxOut{}:
      Bool.pick(Tx, is_cp(ch, 34), TxIn{}, Bool.pick(Tx, is_ws(ch), TxWs{}, TxOut{}))
    case TxIn{}:
      Bool.pick(Tx, is_cp(ch, 92), TxEsc{}, Bool.pick(Tx, is_cp(ch, 34), TxOut{}, TxIn{}))
    case TxEsc{}:
      TxIn{}
    case TxWs{}:
      TxWs{}

# the scan of every character, in order
def tx.run(cs: List<&2, Char>, st: Tx) -> Tx:
  match cs:
    case Nil{}:
      st
    case Con{hd, tl}:
      tx.run(tl, tx.step(st, hd))

# whether a scan never met whitespace outside strings
def tx.ok(st: Tx) -> Bool:
  match st:
    case TxWs{}:
      False{}
    case _:
      True{}

# whether a text holds no whitespace outside its strings
def ws_free(txt: String) -> Bool:
  tx.ok(tx.run(String.to_list(txt), TxOut{}))

# every character is whitespace
def all_ws(+txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{ch, tl}:
      Bool.and(is_ws(ch), all_ws(tl))

# a character that can stand in a bare word: not whitespace, not one of the
# structural characters `[ ] { } : ,` (§2), not a quotation mark or a
# reverse solidus
def word_char(+ch: Char) -> Bool:
  Bool.not(Bool.or(is_ws(ch), Bool.or(is_cp(ch, 91), Bool.or(is_cp(ch, 93), Bool.or(is_cp(ch, 123),
    Bool.or(is_cp(ch, 125), Bool.or(is_cp(ch, 58), Bool.or(is_cp(ch, 44), Bool.or(is_cp(ch, 34), is_cp(ch, 92))))))))))

# every character can stand in a bare word
def word_chars(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      Bool.and(word_char(ch), word_chars(tl))

# a bare word: a text of one or more word characters
def bare(+txt: String) -> Bool:
  match txt:
    case SNil{}:
      False{}
    case SCon{ch, tl}:
      word_chars(ch <> String.to_list(tl))

# the literal names, lowercase (§3), or a number (§6)
def lit_or_num(+txt: String) -> Bool:
  Bool.or(String.eq(txt, "null"), Bool.or(String.eq(txt, "true"), Bool.or(String.eq(txt, "false"),
    number(String.to_list(txt)))))

# whether a parse succeeded
def is_some(mb: Maybe<&2, V.Json>) -> Bool:
  match mb:
    case None{}:
      False{}
    case Some{_}:
      True{}

# a raw character a string keeps as itself: not a quotation mark, not a
# reverse solidus, not a control below U+0020 (§7)
def raw_char(+ch: Char) -> Bool:
  Bool.not(Bool.or(is_cp(ch, 34), Bool.or(is_cp(ch, 92), U32.is_lt(Char.to_u32(ch), 32))))

# every character a string keeps as itself
def raw_ok(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      Bool.and(raw_char(ch), raw_ok(tl))

# the character a two-character escape stands for, RFC 8259 §7: \" \\ \/
# \b \f \n \r \t; none for any other character after a backslash
def unesc(+ch: Char) -> Maybe<&2, Char>:
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 34), Some{'"'},
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 92), Some{'\\'},
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 47), Some{'/'},
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 98), Some{Char.from_u32(8)},
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 102), Some{Char.from_u32(12)},
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 110), Some{'\n'},
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 114), Some{'\r'},
  Bool.pick(Maybe<&2, Char>, is_cp(ch, 116), Some{'\t'},
    None{}))))))))

# a hexadecimal digit: 0 to 9, A to F, a to f (§7)
def hexd(+ch: Char) -> Bool:
  Bool.or(Bool.and(U32.is_ge(Char.to_u32(ch), 48), U32.is_le(Char.to_u32(ch), 57)),
    Bool.or(Bool.and(U32.is_ge(Char.to_u32(ch), 65), U32.is_le(Char.to_u32(ch), 70)),
      Bool.and(U32.is_ge(Char.to_u32(ch), 97), U32.is_le(Char.to_u32(ch), 102))))

# a hexadecimal digit's value
def hexv(+ch: Char) -> U32:
  +x = Char.to_u32(ch)
  Bool.pick(U32, U32.is_le(x, 57), (x - 48 : U32), Bool.pick(U32, U32.is_ge(x, 97), (x - 87 : U32), (x - 55 : U32)))

# one more hexadecimal digit, in base 16
def hex.acc(acc: U32, +ch: Char) -> U32:
  (acc * 16 + hexv(ch) : U32)

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
          Bool.and(hexd(hd), hexn(p, tl))

# the code point four hexadecimal digits spell
def hex4(+aa: Char, +bb: Char, +cc: Char, +dd: Char) -> U32:
  hex.acc(hex.acc(hex.acc(hex.acc(0, aa), bb), cc), dd)

# a high surrogate, D800 to DBFF
def in_hi(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 55296), U32.is_le(cp, 56319))

# D800 to DFFF's upper half, DC00 to DFFF
def in_lo(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 56320), U32.is_le(cp, 57343))

# a low surrogate: in DC00 to DFFF, and so not a high one
def lo_sur(+cp: U32) -> Bool:
  Bool.and(Bool.not(in_hi(cp)), in_lo(cp))

# a code point that is no surrogate
def non_sur(+cp: U32) -> Bool:
  Bool.and(Bool.not(in_hi(cp)), Bool.not(in_lo(cp)))

# the code point a high and a low surrogate stand for, UTF-16's rule
def pair(hi: U32, lo: U32) -> U32:
  U32.add(65536, U32.add(U32.mul(U32.sub(hi, 55296), 1024), U32.sub(lo, 56320)))

# whether a text starts with nn + 1 more hexadecimal digits that, added in
# base 16 to acc, spell a low surrogate
def lo_tail(cs: List<&2, Char>, nn: Nat, acc: U32) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case +hd <> tl:
      match nn:
        case 0n:
          Bool.and(hexd(hd), lo_sur(hex.acc(acc, hd)))
        case 1n+p:
          Bool.and(hexd(hd), lo_tail(tl, p, hex.acc(acc, hd)))

# whether a text starts with u and a low surrogate's four hexadecimal digits
def lo_next.u(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case hd <> tl:
      Bool.and(is_cp(hd, 117), lo_tail(tl, 3n, 0))

# whether a text starts with a low surrogate's \u escape
def lo_next(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case hd <> tl:
      Bool.and(is_cp(hd, 92), lo_next.u(tl))

# the character a Maybe holds, or dflt
def some_or(mb: Maybe<&2, Char>, dflt: Char) -> Char:
  match mb:
    case None{}:
      dflt
    case Some{ch}:
      ch

# whether a Maybe holds a character
def has_char(mb: Maybe<&2, Char>) -> Bool:
  match mb:
    case None{}:
      False{}
    case Some{_}:
      True{}

# one piece of a string's spelling between its quotation marks (§7): a raw
# character, a two-character escape, a \u escape, or a high and a low
# surrogate's \u escapes
type Piece is Data:
  PRaw{ch: Char}
  PEsc{ch: Char}
  PU{aa: Char, bb: Char, cc: Char, dd: Char}
  PPair{h1: Char, h2: Char, h3: Char, h4: Char, l1: Char, l2: Char, l3: Char, l4: Char}

# how a piece is written
def piece.text(pc: Piece) -> String:
  match pc:
    case PRaw{ch}:
      SCon{ch, ""}
    case PEsc{ch}:
      SCon{'\\', SCon{ch, ""}}
    case PU{aa, bb, cc, dd}:
      SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, ""}}}}}}
    case PPair{h1, h2, h3, h4, l1, l2, l3, l4}:
      SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3,
        SCon{l4, ""}}}}}}}}}}}}

# whether a piece is well spelled: a raw character a string keeps, one of the
# two-character escapes, four hex digits of a code point that is no
# surrogate, or four of a high surrogate and then four of a low one
def piece.ok(pc: Piece) -> Bool:
  match pc:
    case PRaw{+ch}:
      raw_char(ch)
    case PEsc{+ch}:
      has_char(unesc(ch))
    case PU{+aa, +bb, +cc, +dd}:
      Bool.and(Bool.and(hexd(aa), Bool.and(hexd(bb), Bool.and(hexd(cc), hexd(dd)))), non_sur(hex4(aa, bb, cc, dd)))
    case PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      Bool.and(Bool.and(hexd(h1), Bool.and(hexd(h2), Bool.and(hexd(h3), hexd(h4)))),
        Bool.and(Bool.and(hexd(l1), Bool.and(hexd(l2), Bool.and(hexd(l3), hexd(l4)))),
          Bool.and(in_hi(hex4(h1, h2, h3, h4)), lo_sur(hex4(l1, l2, l3, l4)))))

# the character a piece stands for
def piece.char(pc: Piece) -> Char:
  match pc:
    case PRaw{ch}:
      ch
    case PEsc{+ch}:
      some_or(unesc(ch), ch)
    case PU{+aa, +bb, +cc, +dd}:
      Char.from_u32(hex4(aa, bb, cc, dd))
    case PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      Char.from_u32(pair(hex4(h1, h2, h3, h4), hex4(l1, l2, l3, l4)))

# how pieces are written, one after another
def spell(ps: List<&2, Piece>) -> String:
  match ps:
    case Nil{}:
      ""
    case pc <> tl:
      piece.text(pc) ++ spell(tl)

# the characters pieces stand for
def spelled(ps: List<&2, Piece>) -> String:
  match ps:
    case Nil{}:
      ""
    case pc <> tl:
      SCon{piece.char(pc), spelled(tl)}

# whether every piece is well spelled
def spell_ok(ps: List<&2, Piece>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case pc <> tl:
      Bool.and(piece.ok(pc), spell_ok(tl))

# get on a parsed value, with the value found read out as owned strings
def get_m(mb: Maybe<&2, V.Json>, +key: String) -> Maybe<&2, V.Json>:
  match mb:
    case None{}:
      None{}
    case Some{jj}:
      Some{own(Ezjson.get(jj, key))}

# a derivation of RFC 8259's value rule (§3 to §7), whitespace included: a
# literal name or a number (§3, §6), a string of pieces (§7), an empty array
# or object, or one with its first element or member (§4, §5), and the cells
# after it: the end, then a comma and the next element or member. The
# whitespace fields sit where §2 allows whitespace: after `[` and `{`, around
# `:` and `,`, and before `]` and `}`
type Gv is Data:
  GWord{w: String}
  GStr{ps: List<&2, Piece>}
  GArr0{w0: String}
  GArr{w0: String, vv: Gv, w1: String, rr: Gv}
  GObj0{w0: String}
  GObj{w0: String, ps: List<&2, Piece>, w1: String, w2: String, vv: Gv, w3: String, rr: Gv}
  GEnd{}
  GNext{w2: String, vv: Gv, w1: String, rr: Gv}
  GNextM{w4: String, ps: List<&2, Piece>, w1: String, w2: String, vv: Gv, w3: String, rr: Gv}

# where a derivation stands: a value, an array's cells after an element, or
# an object's cells after a member
type GK is Data:
  GKVal{}
  GKArr{}
  GKObj{}

# the text a derivation spells
def g.text(gg: Gv) -> String:
  match gg:
    case GWord{w}:
      w
    case GStr{ps}:
      "\"" ++ spell(ps) ++ "\""
    case GArr0{w0}:
      "[" ++ w0 ++ "]"
    case GArr{w0, vv, w1, rr}:
      "[" ++ w0 ++ g.text(vv) ++ w1 ++ g.text(rr) ++ "]"
    case GObj0{w0}:
      "{" ++ w0 ++ "}"
    case GObj{w0, ps, w1, w2, vv, w3, rr}:
      "{" ++ w0 ++ "\"" ++ spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ g.text(vv) ++ w3 ++ g.text(rr) ++ "}"
    case GEnd{}:
      ""
    case GNext{w2, vv, w1, rr}:
      "," ++ w2 ++ g.text(vv) ++ w1 ++ g.text(rr)
    case GNextM{w4, ps, w1, w2, vv, w3, rr}:
      "," ++ w4 ++ "\"" ++ spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ g.text(vv) ++ w3 ++ g.text(rr)

# whether a derivation follows the rules where it stands: words are literal
# names or numbers, strings are well spelled, whitespace is whitespace, and
# each cell is one that may stand there
def g.ok(gg: Gv, kk: GK) -> Bool:
  match gg kk:
    case GWord{+w} GKVal{}:
      lit_or_num(w)
    case GStr{ps} GKVal{}:
      spell_ok(ps)
    case GArr0{+w0} GKVal{}:
      all_ws(w0)
    case GArr{+w0, vv, +w1, rr} GKVal{}:
      Bool.and(all_ws(w0), Bool.and(g.ok(vv, GKVal{}), Bool.and(all_ws(w1), g.ok(rr, GKArr{}))))
    case GObj0{+w0} GKVal{}:
      all_ws(w0)
    case GObj{+w0, ps, +w1, +w2, vv, +w3, rr} GKVal{}:
      Bool.and(all_ws(w0), Bool.and(spell_ok(ps), Bool.and(all_ws(w1), Bool.and(all_ws(w2), Bool.and(g.ok(vv,
        GKVal{}), Bool.and(all_ws(w3), g.ok(rr, GKObj{})))))))
    case GEnd{} GKArr{}:
      True{}
    case GNext{+w2, vv, +w1, rr} GKArr{}:
      Bool.and(all_ws(w2), Bool.and(g.ok(vv, GKVal{}), Bool.and(all_ws(w1), g.ok(rr, GKArr{}))))
    case GEnd{} GKObj{}:
      True{}
    case GNextM{+w4, ps, +w1, +w2, vv, +w3, rr} GKObj{}:
      Bool.and(all_ws(w4), Bool.and(spell_ok(ps), Bool.and(all_ws(w1), Bool.and(all_ws(w2), Bool.and(g.ok(vv,
        GKVal{}), Bool.and(all_ws(w3), g.ok(rr, GKObj{})))))))
    case _ _:
      False{}

# a literal name or a number as a value
def g.word(+txt: String) -> V.Json:
  Bool.pick(V.Json, String.eq(txt, "null"), V.JNull{},
    Bool.pick(V.Json, String.eq(txt, "true"), V.JBool{True{}},
      Bool.pick(V.Json, String.eq(txt, "false"), V.JBool{False{}}, V.JNum{txt})))

# the value a derivation stands for, strings decoded
def g.val(gg: Gv) -> V.Json:
  match gg:
    case GWord{w}:
      g.word(w)
    case GStr{ps}:
      V.JStr{spelled(ps)}
    case GArr0{_}:
      V.JArr{V.JNil{}}
    case GArr{_, vv, _, rr}:
      V.JArr{V.JCons{g.val(vv), g.val(rr)}}
    case GObj0{_}:
      V.JObj{V.JNil{}}
    case GObj{_, ps, _, _, vv, _, rr}:
      V.JObj{V.JPair{spelled(ps), g.val(vv), g.val(rr)}}
    case GEnd{}:
      V.JNil{}
    case GNext{_, vv, _, rr}:
      V.JCons{g.val(vv), g.val(rr)}
    case GNextM{_, ps, _, _, vv, _, rr}:
      V.JPair{spelled(ps), g.val(vv), g.val(rr)}

# whether whitespace, a derivation and whitespace are RFC 8259's JSON-text
# rule (§2): ws value ws
def derived(+wa: String, gg: Gv, +wb: String) -> Bool:
  Bool.and(all_ws(wa), Bool.and(g.ok(gg, GKVal{}), all_ws(wb)))

# where a scan for raw controls in strings is: outside strings, inside one,
# just after a backslash inside one, or past a raw control inside one (§7)
type Cs is Data:
  CsOut{}
  CsIn{}
  CsEsc{}
  CsHit{}

# one character of the scan
def cs.step(st: Cs, +ch: Char) -> Cs:
  match st:
    case CsOut{}:
      Bool.pick(Cs, is_cp(ch, 34), CsIn{}, CsOut{})
    case CsIn{}:
      Bool.pick(Cs, is_cp(ch, 34), CsOut{}, Bool.pick(Cs, is_cp(ch, 92), CsEsc{}, Bool.pick(Cs,
        U32.is_lt(Char.to_u32(ch), 32), CsHit{}, CsIn{})))
    case CsEsc{}:
      CsIn{}
    case CsHit{}:
      CsHit{}

# the scan of every character, in order
def cs.run(cs: List<&2, Char>, st: Cs) -> Cs:
  match cs:
    case Nil{}:
      st
    case Con{hd, tl}:
      cs.run(tl, cs.step(st, hd))

# whether a scan met a raw control inside a string
def cs.hit(st: Cs) -> Bool:
  match st:
    case CsHit{}:
      True{}
    case _:
      False{}

# whether a text holds a raw control U+0000 to U+001F inside a string
def raw_ctl(txt: String) -> Bool:
  cs.hit(cs.run(String.to_list(txt), CsOut{}))

# at most `left` characters, counted down in a U32
def bounded(+txt: String, +left: U32) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{_, tl}:
      Bool.and(Bool.not(U32.is_zero(left)), bounded(tl, U32.sub(left, 1)))

# at most 2^32 - 1 characters: short enough that no count of them wraps a U32
def short(+txt: String) -> Bool:
  bounded(txt, 4294967295)

# LAW: as_bool reads back the boolean bool built
# JSON-TREE-1
law as_bool_bool:
  for flag: Bool
  {Ezjson.as_bool(Ezjson.bool(flag)) == Some{flag} : Maybe<&2, Bool>}

# LAW: as_str reads back the string str built
# JSON-TREE-1
law as_str_str:
  for txt: String
  {Ezjson.as_str(Ezjson.str(txt)) == Some{txt} : Maybe<&2, String>}

# LAW: as_num reads back the text num built from a JSON number
# JSON-TREE-1
law as_num_num:
  for +txt: String
  for h_ok: {V.num.ok(txt) == True{} : Bool}
  {Ezjson.as_num(Ezjson.num(txt)) == Some{txt} : Maybe<&2, String>}

# LAW: as_bool is some exactly on a boolean
# JSON-TREE-2
law as_bool_kind:
  for +val: V.Json
  {Maybe.is_some(&2, Bool, Ezjson.as_bool(val)) == is_bool(val) : Bool}

# LAW: as_str is some exactly on a string, owned or a span
# JSON-TREE-2
law as_str_kind:
  for +val: V.Json
  {Maybe.is_some(&2, String, Ezjson.as_str(val)) == is_str(val) : Bool}

# LAW: as_num is some exactly on a number
# JSON-TREE-2
law as_num_kind:
  for +val: V.Json
  {Maybe.is_some(&2, String, Ezjson.as_num(val)) == is_num(val) : Bool}

# LAW: as_u32 is none on every value that is not a number
# JSON-TREE-2
law as_u32_kind:
  for +val: V.Json
  for h_kind: {is_num(val) == False{} : Bool}
  {Ezjson.as_u32(val) == None{} : Maybe<&2, U32>}

# LAW: as_f32 is none on every value that is not a number
# JSON-TREE-2
law as_f32_kind:
  for +val: V.Json
  for h_kind: {is_num(val) == False{} : Bool}
  {Ezjson.as_f32(val) == None{} : Maybe<&2, F32>}

# LAW: num of a JSON number keeps its text
# JSON-NUM-3
law num_keeps:
  for +txt: String
  for h_ok: {V.num.ok(txt) == True{} : Bool}
  {Ezjson.num(txt) == V.JNum{txt} : V.Json}

# LAW: num of any other text is null
# JSON-NUM-3
law num_null:
  for +txt: String
  for h_bad: {V.num.ok(txt) == False{} : Bool}
  {Ezjson.num(txt) == Ezjson.null() : V.Json}

# LAW: at on a value that is not an array is null, at every index
# JSON-TREE-3
law at_not_arr:
  for +val: V.Json
  for idx: U32
  for h_kind: {is_arr(val) == False{} : Bool}
  {Ezjson.at(val, idx) == Ezjson.null() : V.Json}

# LAW: at on an array is the element at that index, and null past the end
# JSON-TREE-3
law at_arr:
  for +xs: List<&2, V.Json>
  for idx: U32
  {Ezjson.at(Ezjson.arr(xs), idx) == nth(xs, U32.to_nat(idx)) : V.Json}

# LAW: get on a value that is not an object is null, for every key
# JSON-TREE-4
law get_not_obj:
  for +val: V.Json
  for key: String
  for h_kind: {is_obj(val) == False{} : Bool}
  {Ezjson.get(val, key) == Ezjson.null() : V.Json}

# LAW: a number whose F32 read is finite reads as that F32
# JSON-TREE-7
law as_f32_fits:
  for +raw: String
  for +xx: F32
  for h_read: {F32.read(raw) == Some{xx} : Maybe<&2, F32>}
  for h_fin: {F32.is_le(F32.abs(xx), 3.4028235e38) == True{} : Bool}
  {Ezjson.as_f32(V.JNum{raw}) == Some{xx} : Maybe<&2, F32>}

# LAW: a number too large for F32 reads as none, not as an infinity
# JSON-TREE-7
law as_f32_overflow:
  for +raw: String
  for +xx: F32
  for h_read: {F32.read(raw) == Some{xx} : Maybe<&2, F32>}
  for h_inf: {F32.is_le(F32.abs(xx), 3.4028235e38) == False{} : Bool}
  {Ezjson.as_f32(V.JNum{raw}) == None{} : Maybe<&2, F32>}

# LAW: a number F32 cannot read reads as none
# JSON-TREE-7
law as_f32_unread:
  for +raw: String
  for h_read: {F32.read(raw) == None{} : Maybe<&2, F32>}
  {Ezjson.as_f32(V.JNum{raw}) == None{} : Maybe<&2, F32>}

# LAW: an object with no pairs reads null at every key
# JSON-TREE-4
law get_empty:
  for key: String
  {Ezjson.get(Ezjson.obj([]), key) == Ezjson.null() : V.Json}

# LAW: get reads the first pair's value when its key is the key asked for
# JSON-TREE-4
law get_hit:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_eq: {k2 == key : String}
  {Ezjson.get(Ezjson.obj((k2, vv) <> ps), key) == vv : V.Json}

# LAW: get skips a first pair whose key differs and reads the rest
# JSON-TREE-4
law get_miss:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_ne: {k2 != key : String}
  {Ezjson.get(Ezjson.obj((k2, vv) <> ps), key) == Ezjson.get(Ezjson.obj(ps), key) : V.Json}

# LAW: has is false on a value that is not an object, for every key
# JSON-TREE-8
law has_not_obj:
  for +val: V.Json
  for key: String
  for h_kind: {is_obj(val) == False{} : Bool}
  {Ezjson.has(val, key) == False{} : Bool}

# LAW: an object with no pairs has no key
# JSON-TREE-8
law has_empty:
  for key: String
  {Ezjson.has(Ezjson.obj([]), key) == False{} : Bool}

# LAW: an object has a key when its first key is that key
# JSON-TREE-8
law has_hit:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_eq: {k2 == key : String}
  {Ezjson.has(Ezjson.obj((k2, vv) <> ps), key) == True{} : Bool}

# LAW: an object whose first key differs has the key exactly when the rest has it
# JSON-TREE-8
law has_miss:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_ne: {k2 != key : String}
  {Ezjson.has(Ezjson.obj((k2, vv) <> ps), key) == Ezjson.has(Ezjson.obj(ps), key) : Bool}

# LAW: len of an array is how many elements built it
# JSON-TREE-9
law len_arr:
  for xs: List<&2, V.Json>
  {Ezjson.len(Ezjson.arr(xs)) == U32.from_nat(List.length(&2, V.Json, xs)) : U32}

# LAW: len of an object is how many pairs built it
# JSON-TREE-9
law len_obj:
  for ps: List<&1, String & V.Json>
  {Ezjson.len(Ezjson.obj(ps)) == U32.from_nat(List.length(&1, String & V.Json, ps)) : U32}

# LAW: len is 0 on every value that is neither an array nor an object
# JSON-TREE-9
law len_scalar:
  for +val: V.Json
  for h_arr: {is_arr(val) == False{} : Bool}
  for h_obj: {is_obj(val) == False{} : Bool}
  {Ezjson.len(val) == 0 : U32}

# LAW: null, a boolean and a string are well-formed
# JSON-PRINT-3
law wf_scalars:
  for flag: Bool
  for txt: String
  {Bool.and(V.wf(Ezjson.null()), Bool.and(V.wf(Ezjson.bool(flag)), V.wf(Ezjson.str(txt))))
    == True{} : Bool}

# LAW: num builds a well-formed value from every text
# JSON-PRINT-3
law wf_num:
  for +txt: String
  {V.wf(Ezjson.num(txt)) == True{} : Bool}

# LAW: an array of well-formed values is well-formed
# JSON-PRINT-3
law wf_arr:
  for xs: List<&2, V.Json>
  for h_all: {all_wf(xs) == True{} : Bool}
  {V.wf(Ezjson.arr(xs)) == True{} : Bool}

# LAW: an object of well-formed values is well-formed
# JSON-PRINT-3
law wf_obj:
  for ps: List<&1, String & V.Json>
  for h_all: {all_wf_pairs(ps) == True{} : Bool}
  {V.wf(Ezjson.obj(ps)) == True{} : Bool}

# LAW: print then parse gives back a value `same` as the one printed, with
# every code point that is not a Unicode scalar value replaced by U+FFFD
# JSON-PRINT-1
law print_parse:
  for +val: V.Json
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_s: {short(Ezjson.print(val)) == True{} : Bool}
  {own_m(Ezjson.parse(Ezjson.print(val))) == Some{fixv(own(val))} : Maybe<&2, V.Json>}

# LAW: a parsed value prints with no whitespace outside strings
# JSON-PRINT-2
law print_compact:
  for +txt: String
  for +jj: V.Json
  for e_p: {Ezjson.parse(txt) == Some{jj} : Maybe<&2, V.Json>}
  {ws_free(Ezjson.print(jj)) == True{} : Bool}

# LAW: a parsed value printed, parsed again and printed again, prints the same
# JSON-PRINT-2
law print_stable:
  for +txt: String
  for +jj: V.Json
  for e_p: {Ezjson.parse(txt) == Some{jj} : Maybe<&2, V.Json>}
  for h_s: {short(Ezjson.print(jj)) == True{} : Bool}
  {print_m(Ezjson.parse(Ezjson.print(jj))) == Some{Ezjson.print(jj)} : Maybe<&2, String>}

# LAW: every value parse returns is well-formed
# JSON-PRINT-3
law parse_wf:
  for +txt: String
  {wf_m(Ezjson.parse(txt)) == True{} : Bool}

# LAW: get reads a value as it reads the value with its spans read out
# JSON-TREE-5
law get_same:
  for +val: V.Json
  for +key: String
  {own(Ezjson.get(val, key)) == Ezjson.get(own(val), key) : V.Json}

# LAW: at reads a value as it reads the value with its spans read out
# JSON-TREE-5
law at_same:
  for +val: V.Json
  for +idx: U32
  {own(Ezjson.at(val, idx)) == Ezjson.at(own(val), idx) : V.Json}

# LAW: as_str reads a span as its characters
# JSON-TREE-5
law as_str_same:
  for +val: V.Json
  {Ezjson.as_str(val) == Ezjson.as_str(own(val)) : Maybe<&2, String>}

# LAW: as_bool reads a value as it reads the value with its spans read out
# JSON-TREE-5
law as_bool_same:
  for +val: V.Json
  {Ezjson.as_bool(val) == Ezjson.as_bool(own(val)) : Maybe<&2, Bool>}

# LAW: as_num reads a value as it reads the value with its spans read out
# JSON-TREE-5
law as_num_same:
  for +val: V.Json
  {Ezjson.as_num(val) == Ezjson.as_num(own(val)) : Maybe<&2, String>}

# LAW: as_u32 reads a value as it reads the value with its spans read out
# JSON-TREE-5
law as_u32_same:
  for +val: V.Json
  {Ezjson.as_u32(val) == Ezjson.as_u32(own(val)) : Maybe<&2, U32>}

# LAW: as_f32 reads a value as it reads the value with its spans read out
# JSON-TREE-5
law as_f32_same:
  for +val: V.Json
  {Ezjson.as_f32(val) == Ezjson.as_f32(own(val)) : Maybe<&2, F32>}

# LAW: print writes a code point that is not a Unicode scalar value as U+FFFD
# JSON-STR-5
law print_non_scalar:
  for +ch: Char
  for h_non: {non_scalar(Char.to_u32(ch)) == True{} : Bool}
  {Print.escape.char(ch) == String.from_list([Char.from_u32(65533)]) : String}

# LAW: num.ok holds of a text exactly when it matches RFC 8259's number rule
# JSON-NUM-1
law num_grammar:
  for +txt: String
  {V.num.ok(txt) == number(String.to_list(txt)) : Bool}

# LAW: a printed string of scalar values parses back as a string of the same
# characters
# JSON-STR-1
law str_back:
  for +txt: String
  for h_sc: {scalars(txt) == True{} : Bool}
  for h_s: {short(Ezjson.print(Ezjson.str(txt))) == True{} : Bool}
  {str_of(Ezjson.parse(Ezjson.print(Ezjson.str(txt)))) == Some{txt} : Maybe<&2, String>}

# LAW: a text of two values does not parse: a text holds exactly one value
# JSON-TEXT-3
law two_none:
  for +jj: V.Json
  for +kk: V.Json
  for +h_j: {V.wf(jj) == True{} : Bool}
  for +h_k: {V.wf(kk) == True{} : Bool}
  for h_s: {short(Ezjson.print(jj) ++ " " ++ Ezjson.print(kk)) == True{} : Bool}
  {Ezjson.parse(Ezjson.print(jj) ++ " " ++ Ezjson.print(kk)) == None{} : Maybe<&2, V.Json>}

# LAW: a text that starts with U+FEFF, a byte order mark, does not parse
# JSON-TEXT-5
law bom_none:
  for +txt: String
  for h_s: {short(SCon{Char.from_u32(65279), txt}) == True{} : Bool}
  {Ezjson.parse(SCon{Char.from_u32(65279), txt}) == None{} : Maybe<&2, V.Json>}

# LAW: a bare word parses exactly when it is null, true, false or a number
# JSON-TEXT-4
law bare_word:
  for +txt: String
  for h_b: {bare(txt) == True{} : Bool}
  for h_s: {short(txt) == True{} : Bool}
  {is_some(Ezjson.parse(txt)) == lit_or_num(txt) : Bool}

# LAW: a JSON number parses as itself, spelling kept
# JSON-NUM-2
law parse_num:
  for +raw: String
  for h_ok: {V.num.ok(raw) == True{} : Bool}
  for h_s: {short(raw) == True{} : Bool}
  {Ezjson.parse(raw) == Some{V.JNum{raw}} : Maybe<&2, V.Json>}

# LAW: a number prints as its spelling
# JSON-NUM-2
law print_num:
  for +raw: String
  {Ezjson.print(V.JNum{raw}) == raw : String}

# LAW: inside a string, a two-character escape decodes to its character
# JSON-STR-2
law esc_decodes:
  for +pre: String
  for +ch: Char
  for +cc: Char
  for +post: String
  for h_p: {raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_e: {unesc(ch) == Some{cc} : Maybe<&2, Char>}
  for h_q: {raw_ok(String.to_list(post)) == True{} : Bool}
  for h_s: {short("\"" ++ pre ++ SCon{'\\', SCon{ch, post}} ++ "\"") == True{} : Bool}
  {str_of(Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{ch, post}} ++ "\"")) == Some{pre ++ SCon{cc, post}} :
    Maybe<&2, String>}

# LAW: inside a string, a backslash before any character but those of a
# two-character escape or u makes parse None, whatever follows
# JSON-STR-2
law esc_bad:
  for +pre: String
  for +ch: Char
  for +rest: String
  for h_p: {raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_e: {unesc(ch) == None{} : Maybe<&2, Char>}
  for h_u: {is_cp(ch, 117) == False{} : Bool}
  for h_s: {short("\"" ++ pre ++ SCon{'\\', SCon{ch, rest}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{ch, rest}}) == None{} : Maybe<&2, V.Json>}

# LAW: inside a string, \u and four hexadecimal digits of a code point that
# is no surrogate decode to that code point
# JSON-STR-2
law esc_u:
  for +pre: String
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +post: String
  for h_p: {raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_h: {Bool.and(hexd(aa), Bool.and(hexd(bb), Bool.and(hexd(cc), hexd(dd)))) == True{} : Bool}
  for h_n: {non_sur(hex4(aa, bb, cc, dd)) == True{} : Bool}
  for h_q: {raw_ok(String.to_list(post)) == True{} : Bool}
  for h_s: {short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
    post}}}}}} ++ "\"") == True{} : Bool}
  {str_of(Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post}}}}}} ++ "\"")) ==
    Some{pre ++ SCon{Char.from_u32(hex4(aa, bb, cc, dd)), post}} : Maybe<&2, String>}

# LAW: inside a string, a high then a low surrogate escape decode to the one
# code point they stand for
# JSON-STR-2
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
  for h_p: {raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_h: {Bool.and(hexd(h1), Bool.and(hexd(h2), Bool.and(hexd(h3), hexd(h4)))) == True{} : Bool}
  for h_l: {Bool.and(hexd(l1), Bool.and(hexd(l2), Bool.and(hexd(l3), hexd(l4)))) == True{} : Bool}
  for h_hi: {in_hi(hex4(h1, h2, h3, h4)) == True{} : Bool}
  for h_lo: {lo_sur(hex4(l1, l2, l3, l4)) == True{} : Bool}
  for h_q: {raw_ok(String.to_list(post)) == True{} : Bool}
  for h_s: {short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1,
    SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\"") == True{} : Bool}
  {str_of(Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
    SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\"")) ==
    Some{pre ++ SCon{Char.from_u32(pair(hex4(h1, h2, h3, h4), hex4(l1, l2, l3, l4))), post}} : Maybe<&2, String>}

# LAW: inside a string, \u not followed by four hexadecimal digits makes
# parse None, whatever follows
# JSON-STR-2
law esc_u_bad:
  for +pre: String
  for +rest: String
  for h_p: {raw_ok(String.to_list(pre)) == True{} : Bool}
  for h_x: {hexn(4n, String.to_list(rest)) == False{} : Bool}
  for h_s: {short("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}) == None{} : Maybe<&2, V.Json>}

# LAW: inside a string, a low surrogate escape with no high one before it
# makes parse None, whatever follows
# JSON-STR-2
law esc_lo_bad:
  for +pre: String
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +rest: String
  for h_p: {raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_h: {Bool.and(hexd(aa), Bool.and(hexd(bb), Bool.and(hexd(cc), hexd(dd)))) == True{} : Bool}
  for h_lo: {lo_sur(hex4(aa, bb, cc, dd)) == True{} : Bool}
  for h_s: {short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}) == None{} :
    Maybe<&2, V.Json>}

# LAW: inside a string, a high surrogate escape not followed by a low
# surrogate escape makes parse None
# JSON-STR-2
law esc_hi_bad:
  for +pre: String
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +rest: String
  for h_p: {raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_h: {Bool.and(hexd(aa), Bool.and(hexd(bb), Bool.and(hexd(cc), hexd(dd)))) == True{} : Bool}
  for h_hi: {in_hi(hex4(aa, bb, cc, dd)) == True{} : Bool}
  for h_n: {lo_next(String.to_list(rest)) == False{} : Bool}
  for h_s: {short("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}) == True{} : Bool}
  {Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}) == None{} :
    Maybe<&2, V.Json>}

# LAW: inside a string, a raw character other than a control, a quotation
# mark or a reverse solidus is kept as itself
# JSON-STR-3
law raw_kept:
  for +txt: String
  for h_r: {raw_ok(String.to_list(txt)) == True{} : Bool}
  for h_s: {short("\"" ++ txt ++ "\"") == True{} : Bool}
  {str_of(Ezjson.parse("\"" ++ txt ++ "\"")) == Some{txt} : Maybe<&2, String>}

# LAW: get finds an object's member exactly when the key is the characters
# the member's name decodes to, whatever escapes spell it
# JSON-STR-4
law get_decoded:
  for +ps: List<&2, Piece>
  for +val: V.Json
  for +key: String
  for +h_ok: {spell_ok(ps) == True{} : Bool}
  for +h_sc: {scalars(spelled(ps)) == True{} : Bool}
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_s: {short("{\"" ++ spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}") == True{} : Bool}
  {get_m(Ezjson.parse("{\"" ++ spell(ps) ++ "\":" ++ Ezjson.print(val) ++ "}"), key) ==
    Some{Bool.pick(V.Json, String.eq(spelled(ps), key), fixv(own(val)), V.JNull{})} : Maybe<&2, V.Json>}

# LAW: a text RFC 8259's JSON-text rule derives, whitespace, a value and
# whitespace, parses, as the value the derivation stands for
# JSON-TEXT-1
law text_some:
  for +gg: Gv
  for +wa: String
  for +wb: String
  for +h_g: {g.ok(gg, GKVal{}) == True{} : Bool}
  for +h_a: {all_ws(wa) == True{} : Bool}
  for +h_b: {all_ws(wb) == True{} : Bool}
  for h_s: {short(wa ++ g.text(gg) ++ wb) == True{} : Bool}
  {own_m(Ezjson.parse(wa ++ g.text(gg) ++ wb)) == Some{g.val(gg)} : Maybe<&2, V.Json>}

# LAW: a text that parses is RFC 8259's JSON-text rule: whitespace, a
# derivation's text and whitespace
# JSON-TEXT-1
law text_derives:
  for +txt: String
  for +h_s: {short(txt) == True{} : Bool}
  for +h_p: {is_some(Ezjson.parse(txt)) == True{} : Bool}
  exs wa: String
  exs gg: Gv
  exs wb: String
  ({txt == wa ++ g.text(gg) ++ wb : String} & {derived(wa, gg, wb) == True{} : Bool})

# LAW: a raw control U+0000 to U+001F inside a string makes parse None
# JSON-STR-3
law ctl_none:
  for +txt: String
  for h_c: {raw_ctl(txt) == True{} : Bool}
  for h_s: {short(txt) == True{} : Bool}
  {Ezjson.parse(txt) == None{} : Maybe<&2, V.Json>}

# LAW: print escapes a quotation mark as backslash, quotation mark
# JSON-STR-5
law esc_quote:
  for +ch: Char
  for h_eq: {ch == '"' : Char}
  {Print.escape.char(ch) == "\\\"" : String}

# LAW: print escapes a reverse solidus as two
# JSON-STR-5
law esc_backslash:
  for +ch: Char
  for h_eq: {ch == '\\' : Char}
  {Print.escape.char(ch) == "\\\\" : String}

# LAW: print writes a backspace as its two-character escape
# JSON-STR-5
law esc_b:
  for +ch: Char
  for h_eq: {ch == '\u{8}' : Char}
  {Print.escape.char(ch) == "\\b" : String}

# LAW: print writes a form feed as its two-character escape
# JSON-STR-5
law esc_f:
  for +ch: Char
  for h_eq: {ch == '\u{c}' : Char}
  {Print.escape.char(ch) == "\\f" : String}

# LAW: print writes a line feed as its two-character escape
# JSON-STR-5
law esc_n:
  for +ch: Char
  for h_eq: {ch == '\n' : Char}
  {Print.escape.char(ch) == "\\n" : String}

# LAW: print writes a carriage return as its two-character escape
# JSON-STR-5
law esc_r:
  for +ch: Char
  for h_eq: {ch == '\r' : Char}
  {Print.escape.char(ch) == "\\r" : String}

# LAW: print writes a tab as its two-character escape
# JSON-STR-5
law esc_t:
  for +ch: Char
  for h_eq: {ch == '\t' : Char}
  {Print.escape.char(ch) == "\\t" : String}

# LAW: print writes every other scalar value at or above U+0020 as itself
# JSON-STR-5
law esc_plain:
  for +ch: Char
  for h_scalar: {non_scalar(Char.to_u32(ch)) == False{} : Bool}
  for +h_ctl: {U32.is_lt(Char.to_u32(ch), 32) == False{} : Bool}
  for h_quote: {ch != '"' : Char}
  for h_back: {ch != '\\' : Char}
  {Print.escape.char(ch) == String.from_list([ch]) : String}

# LAW: print writes every other control below U+0020 as \u00 and two
# lowercase hex digits
# JSON-STR-5
law esc_ctl:
  for +ch: Char
  for h_ctl: {U32.is_lt(Char.to_u32(ch), 32) == True{} : Bool}
  for h_b: {ch != '\u{8}' : Char}
  for h_f: {ch != '\u{c}' : Char}
  for h_n: {ch != '\n' : Char}
  for h_r: {ch != '\r' : Char}
  for h_t: {ch != '\t' : Char}
  {Print.escape.char(ch) == "\\u00" ++ String.from_list([char_at(hex_lower(), U32.to_nat(U32.div(Char.to_u32(ch), 16))),
    char_at(hex_lower(), U32.to_nat(U32.mod(Char.to_u32(ch), 16)))]) : String}

# LAW: next on a failed cursor is an error and a failed cursor
# JSON-PULL-2
law pull_failed_next:
  for rest: String
  for stack: List<&2, Pull.Frame>
  for done: Bool
  {Ezjson.next(Pull.Cur{rest, stack, done, True{}}) == (Pull.EErr{}, Pull.Cur{"", [], False{}, True{}})
    : (Pull.Ev & Pull.Cur)}

# LAW: skip on a failed cursor is the failed cursor
# JSON-PULL-2
# JSON-PULL-5
law pull_failed_skip:
  for rest: String
  for stack: List<&2, Pull.Frame>
  for +done: Bool
  {Ezjson.skip(Pull.Cur{rest, stack, done, True{}}) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

# LAW: skip after the root is the failed cursor
# JSON-PULL-5
law pull_over_skip:
  for rest: String
  for stack: List<&2, Pull.Frame>
  for +bad: Bool
  {Ezjson.skip(Pull.Cur{rest, stack, True{}, bad}) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

# LAW: text of an owned string is its characters
# JSON-PULL-6
law text_str:
  for body: String
  {Ezjson.text(Pull.EStr{body}) == Some{body} : Maybe<&2, String>}

# LAW: text of an owned key is its characters
# JSON-PULL-6
law text_key:
  for body: String
  {Ezjson.text(Pull.EKey{body}) == Some{body} : Maybe<&2, String>}

# LAW: text of a string span is the first nn characters of its source
# JSON-PULL-6
law text_str_span:
  for +src: String
  for +nn: U32
  {Ezjson.text(Pull.EStrS{src, nn}) == Some{take(src, U32.to_nat(nn))} : Maybe<&2, String>}

# LAW: text of a key span is the first nn characters of its source
# JSON-PULL-6
law text_key_span:
  for +src: String
  for +nn: U32
  {Ezjson.text(Pull.EKeyS{src, nn}) == Some{take(src, U32.to_nat(nn))} : Maybe<&2, String>}

# LAW: text of a number is the first nn characters of its source, its spelling
# JSON-PULL-6
law text_num:
  for +src: String
  for +nn: U32
  {Ezjson.text(Pull.ENum{src, nn}) == Some{take(src, U32.to_nat(nn))} : Maybe<&2, String>}

# LAW: text of every other event is none
# JSON-PULL-6
law text_none:
  for +ev: Pull.Ev
  for h_kind: {has_text(ev) == False{} : Bool}
  {Ezjson.text(ev) == None{} : Maybe<&2, String>}

# LAW: an error from next comes with a failed cursor
# JSON-PULL-2
law pull_err_fails:
  for +cur: Pull.Cur
  for h_err: {is_err(ev_of(Ezjson.next(cur))) == True{} : Bool}
  {failed(cur_of(Ezjson.next(cur))) == True{} : Bool}

# LAW: an end from next comes with an ended cursor
# JSON-PULL-3
law pull_end_ends:
  for +cur: Pull.Cur
  for h_end: {is_end(ev_of(Ezjson.next(cur))) == True{} : Bool}
  {ended(cur_of(Ezjson.next(cur))) == True{} : Bool}

# LAW: next on an ended cursor is the end and the same ended cursor
# JSON-PULL-3
law pull_ended_next:
  for stack: List<&2, Pull.Frame>
  {Ezjson.next(Pull.Cur{"", stack, True{}, False{}}) == (Pull.EEnd{}, Pull.Cur{"", stack, True{}, False{}})
    : (Pull.Ev & Pull.Cur)}

# LAW: skip before an object key, after any whitespace, is the failed cursor
# JSON-PULL-5
law skip_key:
  for +ws: String
  for +key: String
  for fresh: Bool
  for stack: List<&2, Pull.Frame>
  for h_ws: {all_ws(ws) == True{} : Bool}
  {Ezjson.skip(Pull.Cur{ws ++ SCon{'"', key}, Pull.FObj{Pull.SKey{}, fresh} <> stack, False{}, False{}})
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

# LAW: skip at a close bracket, after any whitespace, is the failed cursor
# JSON-PULL-5
law skip_close_arr:
  for +ws: String
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for h_ws: {all_ws(ws) == True{} : Bool}
  {Ezjson.skip(Pull.Cur{ws ++ SCon{']', rest}, stack, False{}, False{}})
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

# LAW: skip at a close brace, after any whitespace, is the failed cursor
# JSON-PULL-5
law skip_close_obj:
  for +ws: String
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for h_ws: {all_ws(ws) == True{} : Bool}
  {Ezjson.skip(Pull.Cur{ws ++ SCon{'}', rest}, stack, False{}, False{}})
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

