# ezjson: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend ezjson/PROOF.bend`
# is the gate.
import Base
import ./value.bend as V
import ./main.bend as Ezjson

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
