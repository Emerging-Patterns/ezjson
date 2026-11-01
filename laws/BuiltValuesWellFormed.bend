# For every value built only from `null`, `bool`, `str`, `num`, `arr` and
# `obj`, or returned by `parse`, `wf` holds
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson

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

# whether a parse result is well-formed: none is, trivially
def wf_m(mb: Maybe<&2, V.Json>) -> Bool:
  match mb:
    case None{}:
      True{}
    case Some{jj}:
      V.wf(jj)

# LAW: null, a boolean and a string are well-formed
law wf_scalars:
  for flag: Bool
  for txt: String
  {Bool.and(V.wf(Ezjson.null()), Bool.and(V.wf(Ezjson.bool(flag)), V.wf(Ezjson.str(txt))))
    == True{} : Bool}

# LAW: num builds a well-formed value from every text
law wf_num:
  for +txt: String
  {V.wf(Ezjson.num(txt)) == True{} : Bool}

# LAW: an array of well-formed values is well-formed
law wf_arr:
  for xs: List<&2, V.Json>
  for h_all: {all_wf(xs) == True{} : Bool}
  {V.wf(Ezjson.arr(xs)) == True{} : Bool}

# LAW: an object of well-formed values is well-formed
law wf_obj:
  for ps: List<&1, String & V.Json>
  for h_all: {all_wf_pairs(ps) == True{} : Bool}
  {V.wf(Ezjson.obj(ps)) == True{} : Bool}

# LAW: every value parse returns is well-formed
law parse_wf:
  for +txt: String
  {wf_m(Ezjson.parse(txt)) == True{} : Bool}
