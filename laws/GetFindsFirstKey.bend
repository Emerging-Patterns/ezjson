# `get(obj(ps), k)` is the value of the first pair in `ps` whose key is `k`,
# and `null()` when there is none; `get(j, k)` is `null()` for every `j` that
# is not an object
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/ObjectTest.bend as D1

# LAW: get on a value that is not an object is null, for every key
law get_not_obj:
  for +val: V.Json
  for key: String
  for h_kind: {D1.is_obj(val) == False{} : Bool}
  {Ezjson.get(val, key) == Ezjson.null() : V.Json}

# LAW: an object with no pairs reads null at every key
law get_empty:
  for key: String
  {Ezjson.get(Ezjson.obj([]), key) == Ezjson.null() : V.Json}

# LAW: get reads the first pair's value when its key is the key asked for
law get_hit:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_eq: {k2 == key : String}
  {Ezjson.get(Ezjson.obj((k2, vv) <> ps), key) == vv : V.Json}

# LAW: get skips a first pair whose key differs and reads the rest
law get_miss:
  for +k2: String
  for vv: V.Json
  for ps: List<&1, String & V.Json>
  for +key: String
  for h_ne: {k2 != key : String}
  {Ezjson.get(Ezjson.obj((k2, vv) <> ps), key) == Ezjson.get(Ezjson.obj(ps), key) : V.Json}
