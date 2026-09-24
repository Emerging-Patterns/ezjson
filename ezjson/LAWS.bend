# ezjson: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend ezjson/PROOF.bend`
# is the gate.
import Base
import ./value.bend as V
import ./main.bend as Ezjson
import ./print.bend as Print

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
