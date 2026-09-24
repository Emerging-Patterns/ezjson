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

