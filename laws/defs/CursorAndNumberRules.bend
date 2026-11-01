# the cursor's events and steps, and the number rule's parts as defs
import Base
import ../../src/value.bend as V
import ../../main.bend as Ezjson
import ../../src/pull.bend as Pull
import ./Digit.bend as D1

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
      when(D1.digit(ch), digits_end(tl), False{})

# 1*DIGIT, then the end
def digits1_end(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(D1.digit(ch), digits_end(tl), False{})

# exp after its e: [ minus / plus ] 1*DIGIT, then the end
def exp_body(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(is_cp(ch, 43), digits1_end(tl),
        when(is_cp(ch, 45), digits1_end(tl),
          when(D1.digit(ch), digits_end(tl), False{})))

# the rest of frac's digits, then [ exp ], then the end
def digits_exp_end(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      when(D1.digit(ch), digits_exp_end(tl), when(is_e(ch), exp_body(tl), False{}))

# frac after its decimal point: 1*DIGIT, then [ exp ], then the end
def frac_body(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(D1.digit(ch), digits_exp_end(tl), False{})

# after an int of `0`: no further digit, then [ frac ] [ exp ], then the end
def zero_rest(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      when(D1.digit(ch), False{},
        when(is_cp(ch, 46), frac_body(tl), when(is_e(ch), exp_body(tl), False{})))

# after digit1-9: *DIGIT, then [ frac ] [ exp ], then the end
def digits_rest(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      when(D1.digit(ch), digits_rest(tl),
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

# the code point a high and a low surrogate stand for, UTF-16's rule
def pair(hi: U32, lo: U32) -> U32:
  U32.add(65536, U32.add(U32.mul(U32.sub(hi, 55296), 1024), U32.sub(lo, 56320)))

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

# what one event of the cursor says, its text read out: a string's, a key's
# or a number's characters, whether a span or owned
type Evt is Data:
  VNull{}
  VBool{b: Bool}
  VNum{raw: String}
  VStr{s: String}
  VKey{s: String}
  VBeginArr{}
  VEndArr{}
  VBeginObj{}
  VEndObj{}
  VEnd{}
  VErr{}

# an event as what it says
def view(ev: Pull.Ev) -> Evt:
  match ev:
    case Pull.ENull{}:
      VNull{}
    case Pull.EBool{bb}:
      VBool{bb}
    case Pull.ENum{src, +nn}:
      VNum{take(src, U32.to_nat(nn))}
    case Pull.EStr{body}:
      VStr{body}
    case Pull.EStrS{src, +nn}:
      VStr{take(src, U32.to_nat(nn))}
    case Pull.EKey{body}:
      VKey{body}
    case Pull.EKeyS{src, +nn}:
      VKey{take(src, U32.to_nat(nn))}
    case Pull.EBeginArr{}:
      VBeginArr{}
    case Pull.EEndArr{}:
      VEndArr{}
    case Pull.EBeginObj{}:
      VBeginObj{}
    case Pull.EEndObj{}:
      VEndObj{}
    case Pull.EEnd{}:
      VEnd{}
    case Pull.EErr{}:
      VErr{}

# a value's events in document order: its scalars, keys, and container
# begins and ends. A value holds no comma or colon event. Read through the
# cells of an array or an object, it gives their elements' or members' events
def events(val: V.Json) -> List<&2, Evt>:
  match val:
    case V.JNull{}:
      [VNull{}]
    case V.JBool{bb}:
      [VBool{bb}]
    case V.JNum{raw}:
      [VNum{raw}]
    case V.JStr{txt}:
      [VStr{txt}]
    case V.JSpan{src, +nn}:
      [VStr{take(src, U32.to_nat(nn))}]
    case V.JArr{items}:
      VBeginArr{} <> List.append(&2, Evt, events(items), [VEndArr{}])
    case V.JObj{pairs}:
      VBeginObj{} <> List.append(&2, Evt, events(pairs), [VEndObj{}])
    case V.JNil{}:
      []
    case V.JCons{hd, tl}:
      List.append(&2, Evt, events(hd), events(tl))
    case V.JPair{kk, vv, rr}:
      VKey{kk} <> List.append(&2, Evt, events(vv), events(rr))
    case V.JBind{src, +nn, vv, rr}:
      VKey{take(src, U32.to_nat(nn))} <> List.append(&2, Evt, events(vv), events(rr))

# the first `left` events next yields from a cursor, one call after another
def pulled(left: Nat, +cur: Pull.Cur) -> List<&2, Evt>:
  match left:
    case 0n:
      []
    case 1n+pp:
      view(ev_of(Ezjson.next(cur))) <> pulled(pp, cur_of(Ezjson.next(cur)))

# the cursor after `left` calls of next
def nexts(left: Nat, cur: Pull.Cur) -> Pull.Cur:
  match left:
    case 0n:
      cur
    case 1n+pp:
      nexts(pp, cur_of(Ezjson.next(cur)))

# What as_u32 reads (laws/AsU32ReadsPlainDigits.bend)

# no character is left
def no_more(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case _ch <> _tl:
      False{}

# the texts as_u32 reads: RFC 8259's int without a minus sign, then the end,
# that is 0, or a digit 1-9 and any more digits: one or more digits, with no
# leading zero unless the text is 0
def decimal(+cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case ch <> tl:
      when(is_cp(ch, 48), no_more(tl), when(digit19(ch), digits_end(tl), False{}))

# half a Nat, rounded down
def half(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      match pp:
        case 0n:
          0n
        case 1n+qq:
          1n+half(qq)
