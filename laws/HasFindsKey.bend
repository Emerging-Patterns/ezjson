# `has(obj(ps), k)` is true exactly when some pair in `ps` has key `k`, and
# `has(j, k)` is false for every `j` that is not an object
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/ObjectTest.bend as D1

# LAW: has is false on a value that is not an object, for every key
law has_not_obj:
  for +val: V.Json
  for key: String
  for h_kind: {D1.is_obj(val) == False{} : Bool}
  {Ezjson.has(val, key) == False{} : Bool}

# LAW: an object with no pairs has no key
law has_empty:
  for key: String
  {Ezjson.has(Ezjson.obj([]), key) == False{} : Bool}

# LAW: an object has a key when its first key is that key
law has_hit:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_eq: {k2 == key : String}
  {Ezjson.has(Ezjson.obj((k2, vv) <> ps), key) == True{} : Bool}

# LAW: an object whose first key differs has the key exactly when the rest has it
law has_miss:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_ne: {k2 != key : String}
  {Ezjson.has(Ezjson.obj((k2, vv) <> ps), key) == Ezjson.has(Ezjson.obj(ps), key) : Bool}
